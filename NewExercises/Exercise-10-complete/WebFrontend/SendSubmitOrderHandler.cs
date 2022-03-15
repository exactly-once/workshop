namespace Orders
{
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
            if (!cart.Submitted)
            {
                cart.Submitted = true;
                await repository.Put(cart.Customer, (cart, version));
            }

            var msg = new SubmitOrder
            {
                Customer = message.Customer,
                CartId = message.CartId,
                Items = cart.Items
            };
            await context.Send(msg);
        }
    }
}