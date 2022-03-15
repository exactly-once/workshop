namespace WebFrontend
{
    using System;
    using System.Threading.Tasks;
    using NServiceBus.Pipeline;

    public class BrokerFailureSimulationBehavior : Behavior<IOutgoingLogicalMessageContext>
    {
        bool failed;

        public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
        {
            if (!failed)
            {
                failed = true;
                throw new Exception("Simulated broker failure");
            }
            await next();

            failed = false;
        }
    }
}
