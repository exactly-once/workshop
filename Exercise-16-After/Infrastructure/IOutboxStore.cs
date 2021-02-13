using System.Threading.Tasks;

public interface IOutboxStore
{
    Task<OutboxState> Get(string transactionId);
    Task Put(string transactionId, OutboxState state);
    Task Delete(string transactionId);
}