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

            order.PaymentBooked = true;

            await repository.Put(message.Customer, (order, version));

            log.Info($"Payment booked for oder {order.Id}");
        }

        static readonly ILog log = LogManager.GetLogger<BookPaymentHandler>();
    }
}