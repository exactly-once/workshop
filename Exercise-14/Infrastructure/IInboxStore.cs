using System.Threading.Tasks;

public interface IInboxStore
{
    Task<bool> HasBeenProcessed(string messageId);
    Task MarkProcessed(string messageId);
}