﻿using System.Threading.Tasks;
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

            order.PaymentBooked = false;

            await repository.Put(message.Customer, (order, version));

            log.Info($"Payment cancelled for oder {order.Id}");

        }

        static readonly ILog log = LogManager.GetLogger<BookPaymentHandler>();
    }
}