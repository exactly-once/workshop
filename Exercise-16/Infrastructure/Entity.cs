using System.Collections.Generic;
using Newtonsoft.Json;

public abstract class Entity
{
    [JsonProperty("id")] public string Id { get; set; }

    public Dictionary<string, string> TransactionIds = new Dictionary<string, string>();
}