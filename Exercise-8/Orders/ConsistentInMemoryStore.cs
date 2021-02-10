using System;
using System.Collections.Generic;
using System.IO;
using System.Threading.Tasks;
using Newtonsoft.Json;

public class ConsistentInMemoryStore<T>
    where T : class, IEntity
{
    Dictionary<string, string> storage = new Dictionary<string, string>();
    Dictionary<string, int> versionInfo = new Dictionary<string, int>();

    JsonSerializerSettings jsonSerializerSettings;

    public ConsistentInMemoryStore()
    {
        jsonSerializerSettings = new JsonSerializerSettings
        {
            TypeNameHandling = TypeNameHandling.Auto,
        };
        jsonSerializerSettings.Converters.Add(new Newtonsoft.Json.Converters.StringEnumConverter());
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
            }
            doc.VersionInfo = versionInfo[doc.Id];
        }
    }

    public void Dump(TextWriter o)
    {
        lock (storage)
        {
            foreach (var entry in storage)
            {
                o.WriteLine(entry.Key + "-> " + entry.Value);
            }
        }
    }
}