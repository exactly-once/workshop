using System.Threading.Tasks;

public interface IInboxStore
{
    //GET
    Task<bool> HasBeenProcessed(string messageId);
    //PUT
    Task MarkProcessed(string messageId);
}

public interface ITokenStore
{
    //GET
    Task<(bool, string)> HasNotBeenProcessed(string messageId);
    //DELETE
    Task MarkProcessed(string messageId, string version);
    //PUT
    Task Create(string messageId);
}