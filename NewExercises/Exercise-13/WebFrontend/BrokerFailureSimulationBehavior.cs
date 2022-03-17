namespace WebFrontend
{
    using System;
    using System.Threading.Tasks;
    using NServiceBus.Pipeline;

    public class BrokerFailureSimulationBehavior : Behavior<ITransportReceiveContext>
    {
        bool failed;

        public override async Task Invoke(ITransportReceiveContext context, Func<Task> next)
        {
            await next();
            if (!failed)
            {
                failed = true;
                throw new Exception("Simulated broker failure");
            }

            failed = false;
        }
    }
}
