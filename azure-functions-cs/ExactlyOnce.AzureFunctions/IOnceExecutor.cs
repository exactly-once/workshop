using System;
using System.Threading;
using System.Threading.Tasks;

namespace ExactlyOnce.AzureFunctions
{
    public interface IOnceExecutor
    {
        Task<TSideEffect> Once<TSideEffect>(Func<TSideEffect> action);
    }

    public interface IOnceExecutor<out TState> where TState : State, new()
    {
        Task<TSideEffect> Once<TSideEffect>(Func<TState, TSideEffect> action);
        Task Once(Action<TState> action);
    }

    class OnceExecutor<TState> : IOnceExecutor<TState> where TState : State, new()
    {
        ExactlyOnceProcessor processor;
        string requestId;
        string stateId;

        public OnceExecutor(ExactlyOnceProcessor processor, string requestId, string stateId)
        {
            this.processor = processor;
            this.requestId = requestId;
            this.stateId = stateId;
        }

        public async Task<TSideEffect> Once<TSideEffect>(Func<TState, TSideEffect> action)
        {
            var maxDelay = TimeSpan.FromSeconds(20);
            var delay = TimeSpan.FromMilliseconds(500);

            do
            {
                try
                {
                    var operationId = $"{typeof(TState).Name}-{stateId}-{requestId}";

                    return await processor.Process(operationId, stateId, action);
                }
                catch (OptimisticConcurrencyFailure)
                {
                    await Task.Delay(delay);

                    delay *= 2;
                }
            } while (delay <= maxDelay);

            throw new OptimisticConcurrencyFailure();

        }

        public Task Once(Action<TState> action)
        {
            return Once(s =>
            {
                action(s);
                return (string)null;
            });
        }
    }

    class OnceExecutor : IOnceExecutor
    {
        IOnceExecutor<Request> processor;

        public OnceExecutor(IOnceExecutor<Request> processor)
        {
            this.processor = processor;
        }

        public Task<TSideEffect> Once<TSideEffect>(Func<TSideEffect> action)
        {
            return processor.Once(_ => action());
        }

        public class Request : State { }
    }

    public class OnceExecutorFactory
    {
        ExactlyOnceProcessor processor;

        public OnceExecutorFactory(ExactlyOnceProcessor processor)
        {
            this.processor = processor;
        }

        public IOnceExecutor<TState> Create<TState>(string requestId, string stateId) where TState : State, new()
        {
            return new OnceExecutor<TState>(processor, requestId, stateId);
        }

        public IOnceExecutor Create(string requestId)
        {
            var executor = new OnceExecutor<OnceExecutor.Request>(processor, requestId, requestId);

            return new OnceExecutor(executor);
        }
    }
}