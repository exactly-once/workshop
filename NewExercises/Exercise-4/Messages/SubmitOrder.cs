using System.Collections.Generic;
using NServiceBus;

namespace Messages
{
    public class SubmitOrder : IMessage
    {
        public string OrderId { get; set; }
        public string Customer { get; set; }
        public List<Filling> Items { get; set; }
    }
}
