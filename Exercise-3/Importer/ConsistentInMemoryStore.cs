using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Newtonsoft.Json;

public class ConsistentInMemoryStore<T>
    where T : class, IEntity
{
    Random r = new Random();
    int count;
    Dictionary<string, string> storage = new Dictionary<string, string>();
    Dictionary<string, int> versionInfo = new Dictionary<string, int>();

    JsonSerializerSettings jsonSerializerSettings = new JsonSerializerSettings
    {
        TypeNameHandling = TypeNameHandling.Auto
    };

    public async Task<IReadOnlyCollection<T>> List()
    {
        lock (storage)
        {
            var values = storage.Values.Select(x =>
            {
                var entity = JsonConvert.DeserializeObject<T>(x, jsonSerializerSettings);
                entity.VersionInfo = versionInfo[entity.Id];
                return entity;
            });

            return values.ToArray();
        }
    }

    public async Task<T> Get(string id)
    {
        T entity = null;
        lock (storage)
        {
            if (storage.TryGetValue(id, out var serializedContainer))
            {
                entity = JsonConvert.DeserializeObject<T>(serializedContainer, jsonSerializerSettings);
                entity.VersionInfo = versionInfo[id];
            }
        }
        return entity;
    }

    public async Task Delete(T doc)
    {
        lock (storage)
        {
            if (count > 2)
            {
                var randomNumber = r.Next(10);
                if (randomNumber > 4)
                {
                    throw new Exception("Database issues");
                }
            }

            if (versionInfo.TryGetValue(doc.Id, out var version))
            {
                if (doc.VersionInfo == null)
                {
                    throw new ConcurrencyException();
                }
                var expectedVersion = (int)doc.VersionInfo;
                if (version != expectedVersion)
                {
                    throw new ConcurrencyException();
                }

                storage.Remove(doc.Id);
                versionInfo.Remove(doc.Id);
            }
            else
            {
                throw new InvalidOperationException("Object does not exist");
            }
        }
    }

    public async Task Put(T doc)
    {
        lock (storage)
        {
            if (versionInfo.TryGetValue(doc.Id, out var version))
            {
                if (doc.VersionInfo == null)
                {
                    throw new ConcurrencyException();
                }
                var expectedVersion = (int)doc.VersionInfo;
                if (version != expectedVersion)
                {
                    throw new ConcurrencyException();
                }
                storage[doc.Id] = JsonConvert.SerializeObject(doc, jsonSerializerSettings);
                versionInfo[doc.Id] = version + 1;
            }
            else
            {
                storage[doc.Id] = JsonConvert.SerializeObject(doc, jsonSerializerSettings);
                versionInfo[doc.Id] = 0;
                count++;
            }
            doc.VersionInfo = versionInfo[doc.Id];
        }
    }
}