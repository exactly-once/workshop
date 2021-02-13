using System.Collections.Generic;
using Newtonsoft.Json;

public abstract class Entity
{
    [JsonProperty("id")] public string Id { get; set; }

    public Dictionary<string, OutboxState> OutboxState { get; set; } = new Dictionary<string, OutboxState>();
}