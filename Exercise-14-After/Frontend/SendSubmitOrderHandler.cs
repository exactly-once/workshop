using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class SendSubmitOrderHandler : IHandleMessages<SendSubmitOrder>
{
    public async Task Handle(SendSubmitOrder message, IMessageHandlerContext context)
    {
        var cart = context.Extensions.Get<ShoppingCart>();

        if (!cart.Submitted)
        {
            await context.Send(new SubmitOrder
            {
                OrderId = cart.Id,
                Items = cart.Items
            });
            cart.Submitted = true;
        }
        else
        {
            log.Info("Duplicate SendSubmitOrder message detected. Ignoring.");
        }
    }

    static readonly ILog log = LogManager.GetLogger<SendSubmitOrderHandler>();
}