using System.Collections.Concurrent;
using System.Threading.Tasks;

class InMemoryDeduplicationStore : IDeduplicationStore
{
    ConcurrentDictionary<string, bool> store = new ConcurrentDictionary<string, bool>();

    public async Task<bool> HasBeenProcessed(string messageId)
    {
        return store.ContainsKey(messageId);
    }

    public async Task MarkProcessed(string messageId)
    {
        store.AddOrUpdate(messageId, true, (key, previous) => true);
    }
}