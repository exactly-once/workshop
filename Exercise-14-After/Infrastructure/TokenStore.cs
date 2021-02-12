using System.Threading.Tasks;
using Microsoft.Azure.Cosmos;

public class TokenStore : Repository<TokenStore.Token>, ITokenStore
{
    public TokenStore(CosmosClient cosmosClient, string databaseId) 
        : base(cosmosClient, databaseId)
    {
    }

    public async Task<(bool, string)> Exists(string tokenId)
    {
        var (token, version) = await Get(tokenId);
        return (version != null, version);
    }

    public Task Create(string tokenId)
    {
        return Put(new Token
        {
            Id = tokenId
        }, null);
    }

    public Task Delete(string tokenId, string version)
    {
        return Delete(new Token
        {
            Id = tokenId
        }, version);
    }

    public class Token : Entity
    {
    }
}