using System.Threading.Tasks;
using Microsoft.Azure.Cosmos;

public class OutboxStore : Repository<OutboxStore.OutboxItem>, IOutboxStore
{
    public OutboxStore(CosmosClient cosmosClient, string databaseId)
        : base(cosmosClient, databaseId)
    {
    }

    public class OutboxItem : Entity
    {
        public OutboxState OutboxState { get; set; }
    }

    public new async Task<OutboxState> Get(string transactionId)
    {
        var (outbox, version) = await base.Get(transactionId);
        return version != null ? outbox.OutboxState : null;
    }

    public Task Put(string transactionId, OutboxState state)
    {
        return Put(new OutboxItem
        {
            OutboxState = state,
            Id = transactionId
        }, null);
    }

    public Task Delete(string transactionId)
    {
        return base.Delete(transactionId, null);
    }
}