using System.Threading.Tasks;
using Messages;
using NServiceBus;

class Importer
{
    public static async Task ImportOrders(ConsistentInMemoryStore<Order> store, IMessageSession messageSession)
    {
        var orders = await store.List();

        foreach (var order in orders)
        {
            //TODO
        }

    }
}