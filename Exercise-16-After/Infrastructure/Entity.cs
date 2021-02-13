using System.Collections.Generic;
using Newtonsoft.Json;

public abstract class Entity
{
    [JsonProperty("id")] public string Id { get; set; }

    public string TransactionId { get; set; }
}