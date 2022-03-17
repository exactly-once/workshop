using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

namespace Orders
{
    public class CancelPaymentHandler : IHandleMessages<CancelPayment>
    {
        private readonly Repository repository;

        public CancelPaymentHandler(Repository repository)
        {
            this.repository = repository;
        }

        public async Task Handle(CancelPayment message, IMessageHandlerContext context)
        {
            var (order, version) = await repository.Get<Order>(message.Customer, message.CartId);

            if (order.ProcessedMessages.Contains(message.Id) == false)
            {
                order.PaymentBooked = false;
                order.ProcessedMessages.Add(message.Id);

                await repository.Put(message.Customer, (order, version));

                log.Info($"Payment cancelled for oder {order.Id}");
            }
            else
            {
                log.Info("Duplicate 'CancelPayment' detected");
            }

            await context.PublishWithId(
                new PaymentCancelled { CustomerId = order.Customer, Value = order.Value },
                Utils.DeterministicGuid(message.Id.ToString(), "Orders").ToString());

        }

        static readonly ILog log = LogManager.GetLogger<BookPaymentHandler>();
    }
}