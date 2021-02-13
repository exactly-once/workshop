using Microsoft.Azure.Cosmos;

class ShoppingCartRepository : Repository<ShoppingCart>
{
    public ShoppingCartRepository(CosmosClient cosmosClient, string databaseId) 
        : base(cosmosClient, databaseId)
    {
    }
}