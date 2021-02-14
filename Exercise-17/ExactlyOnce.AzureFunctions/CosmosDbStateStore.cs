using Microsoft.Azure.Cosmos;
using Newtonsoft.Json;
using System;
using System.IO;
using System.Net;
using System.Threading;
using System.Threading.Tasks;

namespace ExactlyOnce.AzureFunctions
{
    public class CosmosDbStateStore : IStateStore
    {
        Database database;

        public CosmosDbStateStore(CosmosClient cosmosClient, string databaseId)
        {
            database = cosmosClient.CreateDatabaseIfNotExistsAsync(databaseId).GetAwaiter().GetResult();
        }

        public async Task<(TState, string)> Load<TState>(string stateId, CancellationToken cancellationToken = default) where TState : State, new()
        {
            Container container = await database
                .DefineContainer(typeof(TState).Name, "/id")
                .CreateIfNotExistsAsync()
                .ConfigureAwait(false);

            using var response = await container.ReadItemStreamAsync(stateId, new PartitionKey(stateId), cancellationToken: cancellationToken)
                .ConfigureAwait(false);

            if (response.StatusCode == HttpStatusCode.NotFound)
            {
                return (new TState { Id = stateId }, (string)null);
            }

            if (!response.IsSuccessStatusCode)
            {
                throw new Exception(response.ErrorMessage);
            }

            using var streamReader = new StreamReader(response.Content);

            var content = await streamReader.ReadToEndAsync()
                .ConfigureAwait(false);;

            var state = JsonConvert.DeserializeObject<TState>(content);

            return (state, response.Headers.ETag);
        }

        public async Task<string> Upsert<TState>(string stateId, TState value, string version, CancellationToken cancellationToken = default) where TState : State
        {
            Container container = await database
                .DefineContainer(typeof(TState).Name, "/id")
                .CreateIfNotExistsAsync()
                .ConfigureAwait(false);

            try
            {
                var response = await container.UpsertItemAsync(
                        value,
                        requestOptions: new ItemRequestOptions
                        {
                            IfMatchEtag = version,
                        }, cancellationToken: cancellationToken)
                    .ConfigureAwait(false);

                return response.Headers.ETag;
            }
            catch (CosmosException e) when (e.StatusCode == HttpStatusCode.PreconditionFailed || 
                                            e.StatusCode == HttpStatusCode.Conflict)
            {
                throw new OptimisticConcurrencyFailure();
            }
        }
    }
}