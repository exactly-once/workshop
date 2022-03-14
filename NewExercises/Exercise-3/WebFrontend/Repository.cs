using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Threading.Tasks;
using Microsoft.Azure.Cosmos;
using Newtonsoft.Json;

public class Repository
{
    JsonSerializer serializer;
    CosmosClient cosmosClient;
    string databaseId;
    string container;
    Database database;

    public Repository(CosmosClient cosmosClient, string databaseId, string container)
    {
        var jsonSerializerSettings = new JsonSerializerSettings
        {
            TypeNameHandling = TypeNameHandling.Auto,
        };
        jsonSerializerSettings.Converters.Add(new Newtonsoft.Json.Converters.StringEnumConverter());
        serializer = JsonSerializer.Create(jsonSerializerSettings);
        this.cosmosClient = cosmosClient;
        this.databaseId = databaseId;
        this.container = container;
    }

    public async Task Initialize()
    {
        database = await cosmosClient.CreateDatabaseIfNotExistsAsync(databaseId).ConfigureAwait(false);
    }
    async Task<Container> PrepareContainer()
    {
        return await database
            .DefineContainer(container, "/Customer")
            .CreateIfNotExistsAsync()
            .ConfigureAwait(false);
    }

    public async Task<List<T>> List<T>(string partition)
    {
        var container = await PrepareContainer();
        var items = container.GetItemLinqQueryable<T>(true, null, new QueryRequestOptions
        {
            PartitionKey = new PartitionKey(partition)
        })
            .ToList();
        return items;
    }

    public async Task<(T, string)> Get<T>(string partition, string id)
        where T : Entity, new()
    {
        var container = await PrepareContainer();
        using var response = await container.ReadItemStreamAsync(id, new PartitionKey(partition))
            .ConfigureAwait(false);

        if (response.StatusCode == HttpStatusCode.NotFound)
        {
            var newState = new T { Id = id };
            return (newState, (string)null);
        }

        if (!response.IsSuccessStatusCode)
        {
            throw new Exception(response.ErrorMessage);
        }

        using var streamReader = new StreamReader(response.Content);
        using var jsonReader = new JsonTextReader(streamReader);
        var state = serializer.Deserialize<T>(jsonReader);

        return (state, response.Headers.ETag);
    }

    public async Task<string[]> Put(string partition, params (Entity, string)[] items)
    {
        var container = await PrepareContainer();
        var batch = container.CreateTransactionalBatch(new PartitionKey(partition));

        foreach (var (entity, version) in items)
        {
            var payloadStream = new MemoryStream();
            var streamWriter = new StreamWriter(payloadStream);
            serializer.Serialize(streamWriter, entity);
            await streamWriter.FlushAsync();
            payloadStream.Seek(0, SeekOrigin.Begin);

            if (version == null)
            {
                batch.CreateItemStream(payloadStream);
            }
            else
            {
                batch.UpsertItemStream(payloadStream, new TransactionalBatchItemRequestOptions()
                {
                    IfMatchEtag = version
                });
            }
        }

        var response = await batch.ExecuteAsync().ConfigureAwait(false);
        if (!response.IsSuccessStatusCode)
        {
            throw new Exception("Batch execution errors: " + string.Join(", ", response.Select(x => x.StatusCode)));
        }
        
        return response.Select(x => x.ETag).ToArray();
    }

    public async Task<string[]> Put(string partition, params Entity[] items)
    {
        var container = await PrepareContainer();
        var batch = container.CreateTransactionalBatch(new PartitionKey(partition));

        foreach (var entity in items)
        {
            var payloadStream = new MemoryStream();
            var streamWriter = new StreamWriter(payloadStream);
            serializer.Serialize(streamWriter, entity);
            await streamWriter.FlushAsync();
            payloadStream.Seek(0, SeekOrigin.Begin);

            batch.UpsertItemStream(payloadStream);
        }

        var response = await batch.ExecuteAsync().ConfigureAwait(false);
        if (!response.IsSuccessStatusCode)
        {
            throw new Exception(response.ErrorMessage);
        }

        return response.Select(x => x.ETag).ToArray();
    }
}