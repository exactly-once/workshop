using System;
using System.Collections.Generic;
using System.Threading.Tasks;

public class ApplicationServices
{
    readonly Repository repository;

    public ApplicationServices(Repository repository)
    {
        this.repository = repository;
    }

    public async Task<ShoppingCart> Get(string customer, string cartId)
    {
        var (cart, version) = await repository.Get<ShoppingCart>(customer, cartId);
        return cart;
    }

    public Task<List<Order>> GetOrders(string customer)
    {
        return repository.List<Order>(customer);
    }

    public Task CreateCart(string customer, string orderId)
    {
        var cart = new ShoppingCart
        {
            Id = orderId,
            Customer = customer
        };
        return repository.Put(cart.Customer, (cart, null));
    }

    public async Task AddItem(string customer, string orderId, Filling filling)
    {
        var (cart, version) = await repository.Get<ShoppingCart>(customer, orderId);
        if (!cart.Items.Contains(filling))
        {
            cart.Items.Add(filling);
        }
        await repository.Put(cart.Customer, (cart, version));
    }

    public async Task SubmitOrder(string customer, string orderId)
    {
        var (cart, version) = await repository.Get<ShoppingCart>(customer, orderId);

        var order = new Order
        {
            Id = Guid.NewGuid().ToString(),
            Customer = cart.Customer,
            Items = cart.Items
        };

        await repository.Put(cart.Customer, (order, null));
    }
}