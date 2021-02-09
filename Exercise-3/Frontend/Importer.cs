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
            await messageSession.Send(new SubmitOrder
            {
                OrderId = order.Id
            });

            await messageSession.Send(new AddItem
            {
                OrderId = order.Id,
                Filling = order.Filling
            });

            await store.Delete(order);
        }

    }
}