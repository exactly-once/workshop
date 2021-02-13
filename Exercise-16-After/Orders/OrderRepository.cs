using Microsoft.Azure.Cosmos;

class OrderRepository : Repository<Order>
{
    public OrderRepository(CosmosClient cosmosClient, string databaseId) : base(cosmosClient, databaseId)
    {
    }
}