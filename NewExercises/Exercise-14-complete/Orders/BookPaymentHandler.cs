using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

namespace Orders
{
    public class BookPaymentHandler : IHandleMessages<BookPayment>
    {
        private readonly Repository repository;

        public BookPaymentHandler(Repository repository)
        {
            this.repository = repository;
        }

        public async Task Handle(BookPayment message, IMessageHandlerContext context)
        {
            var (order, version) = await repository.Get<Order>(message.Customer, message.CartId);

            if (order.ProcessedMessages.Contains(message.Id) == false)
            {
                order.PaymentBooked = true;
                order.ProcessedMessages.Add(message.Id);

                await repository.Put(message.Customer, (order, version));

                log.Info($"Payment booked for oder {order.Id}");
            }
            else
            {
                log.Info($"Duplicate 'BookPayment' detected OrderId={order.Id}");
            }

            await context.PublishWithId(
                new PaymentBooked {CustomerId = order.Customer, Value = order.Value},
                Utils.DeterministicGuid(message.Id.ToString(), "Orders").ToString());
        }

        static readonly ILog log = LogManager.GetLogger<BookPaymentHandler>();
    }
}