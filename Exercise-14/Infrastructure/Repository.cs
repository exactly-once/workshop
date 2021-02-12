using System;
using System.IO;
using System.Net;
using System.Threading.Tasks;
using Microsoft.Azure.Cosmos;
using Newtonsoft.Json;

public class Repository<T>
    where T : Entity, new()
{
    JsonSerializer serializer;
    CosmosClient cosmosClient;
    string databaseId;
    Database database;

    public Repository(CosmosClient cosmosClient, string databaseId)
    {
        var jsonSerializerSettings = new JsonSerializerSettings
        {
            TypeNameHandling = TypeNameHandling.Auto,
        };
        jsonSerializerSettings.Converters.Add(new Newtonsoft.Json.Converters.StringEnumConverter());
        serializer = JsonSerializer.Create(jsonSerializerSettings);
        this.cosmosClient = cosmosClient;
        this.databaseId = databaseId;
    }

    public async Task Initialize()
    {
        database = await cosmosClient.CreateDatabaseIfNotExistsAsync(databaseId).ConfigureAwait(false);
    }
    async Task<Container> PrepareContainer()
    {
        return await database
            .DefineContainer(typeof(T).Name, "/id")
            .CreateIfNotExistsAsync()
            .ConfigureAwait(false);
    }

    public async Task<(T, string)> Get(string id)
    {
        var container = await PrepareContainer();
        using var response = await container.ReadItemStreamAsync(id, new PartitionKey(id))
            .ConfigureAwait(false);

        if (response.StatusCode == HttpStatusCode.NotFound)
        {
            var newState = new T {Id = id};
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

    public async Task Delete(T value, string version)
    {
        var container = await PrepareContainer();
        await container.DeleteItemStreamAsync(value.Id, new PartitionKey(value.Id), new ItemRequestOptions
        {
            IfMatchEtag = version
        });
    }

    public async Task<string> Put(T doc, string version)
    {
        var container = await PrepareContainer();
        try
        {
            await using (var payloadStream = new MemoryStream())
            await using (var streamWriter = new StreamWriter(payloadStream))
            {
                serializer.Serialize(streamWriter, doc);
                await streamWriter.FlushAsync();
                payloadStream.Seek(0, SeekOrigin.Begin);

                if (version == null)
                {
                    var response = await container.CreateItemStreamAsync(
                            payloadStream,
                            new PartitionKey(doc.Id))
                        .ConfigureAwait(false);

                    if (!response.IsSuccessStatusCode)
                    {
                        throw new Exception(response.ErrorMessage);
                    }

                    return response.Headers.ETag;
                }
                else
                {
                    var response = await container.UpsertItemStreamAsync(
                            payloadStream,
                            new PartitionKey(doc.Id),
                            new ItemRequestOptions
                            {
                                IfMatchEtag = version,
                            })
                        .ConfigureAwait(false);

                    if (!response.IsSuccessStatusCode)
                    {
                        throw new Exception(response.ErrorMessage);
                    }

                    return response.Headers.ETag;
                }
            }

        }
        catch (CosmosException e) when (e.StatusCode == HttpStatusCode.PreconditionFailed ||
                                        e.StatusCode == HttpStatusCode.Conflict)
        {
            throw new ConcurrencyException();
        }
    }
}