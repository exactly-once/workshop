using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using Marketing;
using Messages;
using Messaging.IntegrationTests.Tests;
using NServiceBus;
using NServiceBus.Pipeline;
using NUnit.Framework;

namespace Tests
{
    public class IntegrationTests
    {
        IEndpointInstance ordersEndpoint;
        IEndpointInstance marketingEndpoint;
        Repository ordersRepository;
        Repository marketingRepository;

        Tracer tracer = new Tracer();

        [SetUp]
        public async Task Setup()
        {
            Console.SetOut(TestContext.Progress);

            (ordersEndpoint, ordersRepository) = await Orders.Program.Start((c, r) =>
            {
                c.AssemblyScanner().ExcludeAssemblies("Tests.dll", "Marketing.exe");

                c.Pipeline.Register(new TracingBehavior(), "Trace input and output messages.");

                r.RouteToEndpoint(typeof(SubmitOrder), "Orders");
                r.RouteToEndpoint(typeof(BookPayment), "Orders");
                r.RouteToEndpoint(typeof(CancelPayment), "Orders");
            });

            (marketingEndpoint, marketingRepository) = await Marketing.Program.Start((c, r) =>
            {
                c.AssemblyScanner().ExcludeAssemblies("Tests.dll", "Orders.exe");

                c.Pipeline.Register(new TracingBehavior(), "Trace input and output messages.");
                c.Pipeline.Register(new ImmediateTracingBehavior(), "Trace immediate output messages.");

                c.Pipeline.Register(new DropMessagesBehavior(), "Drops selected messages");
            });

            await tracer.Start();
        }

        [TearDown]
        public async Task CleanUp()
        {
            await ordersEndpoint.Stop();
            await marketingEndpoint.Stop();
            await tracer.Stop();
        }

        [Test]
        public async Task SubmitOder()
        {
            var cartId = Guid.NewGuid().ToString();
            var customerId = Guid.NewGuid().ToString();

            var (conversationId, options) = tracer.Prepare();

            var message = new SubmitOrder
            {
                CartId = cartId,
                Customer = customerId,
                Items = new List<Filling>()
            };

            await ordersEndpoint.Send(message, options);

            await tracer.WaitUntilFinished(conversationId);

            var (order, version) = await ordersRepository.Get<Order>(message.Customer, message.CartId);

            Assert.AreEqual(order.Customer, customerId);
        }

        //ID-based de-duplication. Start with no message id on the commands
        //Add message id to the commands and the ProcessedMessages to the order
        [Test]
        public async Task ChangeStatus()
        {
            var cartId = Guid.NewGuid().ToString();
            var customerId = Guid.NewGuid().ToString();

            var submitOrder = new SubmitOrder {CartId = cartId, Customer = customerId, Items = new List<Filling>()};

            var bookPayment = new BookPayment {Id = Guid.NewGuid(), CartId = cartId, Customer = customerId};

            var cancelPayment = new CancelPayment {Id = Guid.NewGuid(), CartId = cartId, Customer = customerId};

            await SendInOrder(new IMessage[]
                {
                    submitOrder,
                    bookPayment,
                    cancelPayment,
                    bookPayment
                }
            );

            var (order, _) = await ordersRepository.Get<Order>(customerId, cartId);

            Assert.AreEqual(order.PaymentBooked, false);
        }

        //Start with no deterministic message id in the order handler
        [Test]
        public async Task TrackTotalPaymentsValue()
        {
            var cartId = Guid.NewGuid().ToString();
            var customerId = Guid.NewGuid().ToString();

            var submitOrder = new SubmitOrder { CartId = cartId, Customer = customerId, Items = new List<Filling>
                {
                    Filling.Meat,
                    Filling.Mushrooms,
                    Filling.QuarkAndPotatoes
                } };

            var bookPayment = new BookPayment { Id = Guid.NewGuid(), CartId = cartId, Customer = customerId };

            var cancelPayment = new CancelPayment { Id = Guid.NewGuid(), CartId = cartId, Customer = customerId };

            await SendInOrder(new IMessage[]
                {
                    submitOrder,
                    bookPayment,
                    cancelPayment,
                    bookPayment
                }
            );

            var (payment, _) = await marketingRepository.Get<Payments>(customerId, Payments.RowId);

            Assert.AreEqual(0, payment.TotalValue);
        }

        //Start with no deterministic message id in the order handler
        [Test]
        public async Task IssueCouponCardAfterFirst100USDSpent()
        {
            var cartId = Guid.NewGuid().ToString();
            var customerId = Guid.NewGuid().ToString();

            var submitFirstOrder = new SubmitOrder
            {
                CartId = cartId,
                Customer = customerId,
                Items = new List<Filling>
                {
                    Filling.Meat,
                    Filling.Mushrooms,
                    Filling.QuarkAndPotatoes
                }
            };

            var submitSecondOrder = new SubmitOrder
            {
                CartId = cartId,
                Customer = customerId,
                Items = new List<Filling>
                {
                    Filling.Strawberry,
                    Filling.SwissCheese
                }
            };

            var bookFirstPayment = new BookPayment { Id = Guid.NewGuid(), CartId = cartId, Customer = customerId };
            var bookSecondPayment = new BookPayment { Id = Guid.NewGuid(), CartId = cartId, Customer = customerId };

            await SendInOrder(new IMessage[]
                {
                    submitFirstOrder,
                    bookFirstPayment,
                    submitSecondOrder,
                    bookSecondPayment,
                    bookFirstPayment //HINT: this is a retried message
                }
            );

            var (_, version) = await marketingRepository.Get<Coupon>(customerId, Coupon.RowId);

            Assert.IsNotNull(version);
        }

        async Task SendInOrder(IMessage[] messages)
        {
            foreach (var message in messages)
            {
                var (conversationId, options) = tracer.Prepare();

                await ordersEndpoint.Send(message, options);

                await tracer.WaitUntilFinished(conversationId);
            }
        }
        async Task Execute(Func<SendOptions, Task> step)
        {
            var (conversationId, options) = tracer.Prepare();

            await step(options);

            await tracer.WaitUntilFinished(conversationId);
        }
    }

    public class DropMessagesBehavior : Behavior<IOutgoingLogicalMessageContext>
    {
        private bool dropped = false;

        public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
        {
            if (!dropped && context.Message.Instance is GrantCoupon)
            {
                dropped = true;
            }
            else
            {
                await next();
            }
        }
    }
}