namespace Orders
{
    using System;
    using System.Threading.Tasks;
    using Messages;
    using NServiceBus;

    public class SendSubmitOrderHandler : IHandleMessages<SendSubmitOrder>
    {
        Repository repository;

        public SendSubmitOrderHandler(Repository repository)
        {
            this.repository = repository;
        }

        public async Task Handle(SendSubmitOrder message, IMessageHandlerContext context)
        {
            var (cart, version) = await repository.Get<ShoppingCart>(message.Customer, message.CartId);
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
                Customer = message.Customer,
                CartId = message.CartId,
                Items = cart.Items
            };
            var sendOptions = new SendOptions();
            sendOptions.RequireImmediateDispatch();
            await context.Send(msg, sendOptions);

            cart.Submitted = true;
            await repository.Put(cart.Customer, (cart, version));
        }
    }
}