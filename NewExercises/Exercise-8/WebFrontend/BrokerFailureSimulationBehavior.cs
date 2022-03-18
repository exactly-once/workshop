namespace WebFrontend
{
    using System;
    using System.Threading.Tasks;
    using Messages;
    using NServiceBus.Pipeline;

    public class BrokerFailureSimulationBehavior : Behavior<IOutgoingLogicalMessageContext>
    {
        bool failed;

        public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
        {
            await next();

            if (!(context.Message.Instance is SubmitOrder))
            {
                return;
            }

            if (!failed)
            {
                failed = true;
                throw new Exception("Simulated broker failure");
            }
            failed = false;
        }
    }
}
