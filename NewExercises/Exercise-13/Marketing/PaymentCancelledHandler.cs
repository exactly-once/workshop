using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

namespace Marketing
{
    public class PaymentCancelledHandler : IHandleMessages<PaymentCancelled>
    {
        private readonly Repository repository;

        public PaymentCancelledHandler(Repository repository)
        {
            this.repository = repository;
        }

        public async Task Handle(PaymentCancelled message, IMessageHandlerContext context)
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
                        TotalValue = -message.Value
                    };
                }
                else
                {
                    payments.TotalValue -= message.Value;
                }

                payments.ProcessedMessage.Add(context.MessageId);

                await repository.Put(message.CustomerId, (payments, version));

                log.Info($"Processed {nameof(PaymentCancelled)} messageId={context.MessageId}");
            }
            else
            {
                log.Info($"Duplicate detected for {nameof(PaymentCancelled)} messageId={context.MessageId}");
            }
        }

        static readonly ILog log = LogManager.GetLogger<PaymentCancelledHandler>();
    }
}