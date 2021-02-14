using System.Threading;
using System.Threading.Tasks;

namespace ExactlyOnce.AzureFunctions
{
    public interface IStateStore
    {
        Task<(TState, string)> Load<TState>(string stateId, CancellationToken cancellationToken = default) where TState : State, new();

        Task<string> Upsert<TState>(string stateId, TState value, string version, CancellationToken cancellationToken = default) where TState : State;
    }
}