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

public class TokenStore : Repository<TokenStore.Token>, ITokenStore
{
    public TokenStore(CosmosClient cosmosClient, string databaseId)
        : base(cosmosClient, databaseId)
    {
    }

    public async Task<(bool, string)> HasNotBeenProcessed(string messageId)
    {
        if (messageId == null)
        {
            return (true, null);
        }
        var (token, version) = await Get(messageId);
        return (token != null, version);
    }

    public Task MarkProcessed(string messageId, string version)
    {
        if (messageId == null)
        {
            return Task.CompletedTask;
        }
        return Delete(new Token
        {
            Id = messageId
        }, version);
    }

    public Task Create(string messageId)
    {
        return Put(new Token
        {
            Id = messageId
        }, null);
    }

    public class Token : Entity
    {
    }
}