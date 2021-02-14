using System;
using System.Threading;
using System.Threading.Tasks;
using Newtonsoft.Json;

namespace ExactlyOnce.AzureFunctions
{
    public class ExactlyOnceProcessor
    {
        OutboxStore outboxStore;
        IStateStore stateStore;

        public ExactlyOnceProcessor(OutboxStore outboxStore, IStateStore stateStore)
        {
            this.outboxStore = outboxStore;
            this.stateStore = stateStore;
        }

        public async Task<TSideEffect> Process<TState, TSideEffect>(string requestId, string stateId,
            Func<TState, TSideEffect> handle, CancellationToken cancellationToken = default) where TState : State, new()
        {
            var (state, version) = await stateStore.Load<TState>(stateId, cancellationToken)
                .ConfigureAwait(false);

            if (state.TxId != null)
            {
                await FinishTransaction(stateId, state, version, cancellationToken)
                    .ConfigureAwait(false);
            }

            var outboxState = await outboxStore.Get(requestId, cancellationToken);

            if (outboxState != null)
            {
                return JsonConvert.DeserializeObject<TSideEffect>(outboxState.SideEffect);
            }

            var sideEffect = handle(state);

            state.TxId = Guid.NewGuid();

            outboxState = new OutboxItem
            {
                Id = state.TxId.ToString(),
                RequestId = requestId,
                SideEffect = JsonConvert.SerializeObject(sideEffect)
            };

            await outboxStore.Store(outboxState, cancellationToken)
                .ConfigureAwait(false);

            string nextVersion;

            try
            {
                nextVersion = await stateStore.Upsert(stateId, state, version, cancellationToken)
                    .ConfigureAwait(false);
            }
            catch (Exception e) when (!(e is OperationCanceledException))
            {
                await outboxStore.Delete(outboxState.Id, cancellationToken)
                    .ConfigureAwait(false);
                throw;
            }

            await FinishTransaction(stateId, state, nextVersion, cancellationToken)
                .ConfigureAwait(false);

            return sideEffect;
        }

        async Task FinishTransaction<TState>(string stateId, TState state, string version, CancellationToken cancellationToken = default) where TState : State
        {
            if (state.TxId.HasValue == false)
            {
                throw new InvalidOperationException($"No pending transaction for state id {stateId}.");
            }

            await outboxStore.Commit(state.TxId.Value.ToString(), cancellationToken)
                .ConfigureAwait(false);

            state.TxId = null;
            await stateStore.Upsert(stateId, state, version, cancellationToken)
                .ConfigureAwait(false);
        }
    }
}