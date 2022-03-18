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
        var (cart, version) = await repository.Get<ShoppingCart>(customer, cartId);
        if (cart.Submitted)
        {
            throw new Exception("Order already submitted");
        }

        if (!cart.Accepted)
        {
            cart.Accepted = true;
            version = (await repository.Put(cart.Customer, (cart, version)))[0];
        }

        var msg = new SubmitOrder
        {
            Customer = customer,
            CartId = cartId,
            Items = cart.Items
        };
        await session.Send(msg);

        cart.Submitted = true;
        await repository.Put(cart.Customer, (cart, version));


    }
}