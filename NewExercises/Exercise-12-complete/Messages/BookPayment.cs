using System;
using NServiceBus;

namespace Messages
{
    public class BookPayment : ICommand
    {
        public string CartId { get; set; }
        public string Customer { get; set; }
        public Guid Id { get; set; }
    }
}