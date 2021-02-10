using System.Collections.Generic;

public class Order : IEntity
{
    public object VersionInfo { get; set; }
    public string Id { get; set; }
    public List<OrderLine> Lines { get; set; } = new List<OrderLine>();
    public List<string> ProcessedMessages = new List<string>();
    public Dictionary<string, object> OutgoingMessages = new Dictionary<string, object>();
}