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

            if (payments.ProcessedMessage.Contains(context.MessageId))
            {
                log.Info($"Duplicate detected from {nameof(PaymentBooked)} messageId={context.MessageId}");
            }
            else
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

                if (payments.TotalValue >= 100 && payments.TotalValue - message.Value < 100)
                {
                    payments.OutgoingMessages.Add(new GrantCoupon { Customer = message.CustomerId });
                }

                await repository.Put(message.CustomerId, (payments, version));

                log.Info($"Processed {nameof(PaymentBooked)} messageId={context.MessageId}");
            }

            foreach (var outgoingMessage in payments.OutgoingMessages)
            {
                await context.SendImmediately(outgoingMessage);
            }
        }

        static readonly ILog log = LogManager.GetLogger<PaymentBookedHandler>();
    }
}