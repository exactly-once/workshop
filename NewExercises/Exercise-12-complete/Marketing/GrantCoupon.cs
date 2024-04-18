using NServiceBus;

namespace Marketing
{
    public class GrantCoupon : ICommand
    {
        public string Customer { get; set; }
    }
}