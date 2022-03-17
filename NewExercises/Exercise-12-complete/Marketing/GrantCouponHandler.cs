using System.Threading.Tasks;
using NServiceBus;
using NServiceBus.Logging;

namespace Marketing
{
    public class GrantCouponHandler : IHandleMessages<GrantCoupon>
    {
        private readonly Repository repository;

        public GrantCouponHandler(Repository repository)
        {
            this.repository = repository;
        }

        public async Task Handle(GrantCoupon message, IMessageHandlerContext context)
        {
            var (coupon, version) = await repository.Get<Coupon>(message.Customer, Coupon.RowId);

            if (version == null)
            {
                await repository.Put(message.Customer, (new Coupon
                {
                    Customer = message.Customer,
                    Id = Coupon.RowId
                }, null));
            }

            log.Info($"Coupon granted for customer={message.Customer}");
        }

        static readonly ILog log = LogManager.GetLogger<GrantCouponHandler>();
    }
}