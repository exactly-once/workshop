using System.Threading.Tasks;

interface IInboxStore
{
    Task<bool> HasBeenProcessed(string messageId);
    Task MarkProcessed(string messageId);
}