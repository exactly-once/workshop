using System.Linq;
using System.Threading.Tasks;
using Messages;

class OrderRepository : ConsistentInMemoryStore<Order>
{
    public Task<Order> Load(string orderId)
    {
        return Get(orderId);
    }

    public Task Store(Order order)
    {
        return Put(order);
    }
}