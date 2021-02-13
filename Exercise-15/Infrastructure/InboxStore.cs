using System.Threading.Tasks;
using Microsoft.Azure.Cosmos;

public class InboxStore : Repository<InboxStore.InboxItem>, IInboxStore
{
    public InboxStore(CosmosClient cosmosClient, string databaseId) 
        : base(cosmosClient, databaseId)
    {
    }

    public async Task<bool> HasBeenProcessed(string messageId)
    {
        return (await Get(messageId)).Item2 != null;
    }

    public Task MarkProcessed(string messageId)
    {
        return Put(new InboxItem
        {
            Id = messageId
        }, null);
    }

    public class InboxItem : Entity
    {
    }
}