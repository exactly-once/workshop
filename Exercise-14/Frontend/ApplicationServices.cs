using System.Threading.Tasks;
using Messages;
using NServiceBus;

class ApplicationServices
{
    readonly ShoppingCartRepository repository;
    readonly IMessageSession messageSession;

    public ApplicationServices(ShoppingCartRepository repository, IMessageSession messageSession)
    {
        this.repository = repository;
        this.messageSession = messageSession;
    }

    public Task CreateOrder(string orderId)
    {
        var cart = new ShoppingCart
        {
            Id = orderId
        };
        return repository.Put(cart, null);
    }

    public async Task AddItem(string orderId, Filling filling)
    {
        var (cart, version) = await repository.Get(orderId);
        if (!cart.Items.Contains(filling))
        {
            cart.Items.Add(filling);
        }
        await repository.Put(cart, version);
    }

    public async Task RemoveItem(string orderId, Filling filling)
    {
        var (cart, version) = await repository.Get(orderId);
        cart.Items.Remove(filling);
        await repository.Put(cart, version);
    }

    public Task SubmitOrder(string orderId)
    {
        return messageSession.SendLocal(new SendSubmitOrder
        {
            OrderId = orderId
        });
    }
}