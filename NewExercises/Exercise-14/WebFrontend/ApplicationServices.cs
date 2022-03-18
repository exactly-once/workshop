using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using Messages;
using NServiceBus;

public class ApplicationServices
{
    readonly Repository repository;
    readonly IMessageSession session;

    public ApplicationServices(Repository repository, IMessageSession session)
    {
        this.repository = repository;
        this.session = session;
    }

    public async Task<ShoppingCart> Get(string customer, string cartId)
    {
        var (cart, version) = await repository.Get<ShoppingCart>(customer, cartId);
        return cart;
    }

    public Task<List<ShoppingCart>> GetOrders(string customer)
    {
        return repository.List<ShoppingCart>(customer);
    }

    public Task CreateCart(string customer, string cartId)
    {
        var cart = new ShoppingCart
        {
            Id = cartId,
            Customer = customer
        };
        return repository.Put(cart.Customer, (cart, null));
    }

    public async Task AddItem(string customer, string cartId, Filling filling)
    {
        var (cart, version) = await repository.Get<ShoppingCart>(customer, cartId);
        if (!cart.Items.Contains(filling))
        {
            cart.Items.Add(filling);
        }
        await repository.Put(cart.Customer, (cart, version));
    }

    public async Task SubmitOrder(string customer, string cartId)
    {
        var msg = new SendSubmitOrder
        {
            Customer = customer,
            CartId = cartId,
        };
        await session.SendLocal(msg);

        
    }
}