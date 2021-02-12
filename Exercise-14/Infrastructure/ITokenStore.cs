using System.Threading.Tasks;

public interface ITokenStore
{
    Task<(bool, string)> Exists(string tokenId);
    Task Create(string tokenId);
    Task Delete(string tokenId, string version);
}