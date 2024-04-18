using System.Threading.Tasks;

interface IDeduplicationStore
{
    Task<bool> HasBeenProcessed(string messageId);
    Task MarkProcessed(string messageId);
}