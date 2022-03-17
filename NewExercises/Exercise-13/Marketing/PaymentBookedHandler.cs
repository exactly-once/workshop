using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

namespace Marketing
{
    public class PaymentBookedHandler : IHandleMessages<PaymentBooked>
    {
        private readonly Repository repository;

        public PaymentBookedHandler(Repository repository)
        {
            this.repository = repository;
        }
        public async Task Handle(PaymentBooked message, IMessageHandlerContext context)
        {
            var (payments, version) = await repository.Get<Payments>(message.CustomerId, Payments.RowId);

            if (payments.ProcessedMessage.Contains(context.MessageId) == false)
            {
                if (version == null)
                {
                    payments = new Payments
                    {
                        Customer = message.CustomerId,
                        Id = Payments.RowId,
                        TotalValue = message.Value
                    };
                }
                else
                {
                    payments.TotalValue += message.Value;

                }

                payments.ProcessedMessage.Add(context.MessageId);

                await repository.Put(message.CustomerId, (payments, version));

                log.Info($"Processed {nameof(PaymentBooked)} messageId={context.MessageId}");
            }
            else
            {
                log.Info($"Duplicate detected from {nameof(PaymentBooked)} messageId={context.MessageId}");
            }
        }

        static readonly ILog log = LogManager.GetLogger<PaymentBookedHandler>();
    }
}