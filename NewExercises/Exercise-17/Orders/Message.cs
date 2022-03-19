public class Message
{
    public string Id { get; set; }
    public object Payload { get; set; }

    public Message()
    {
    }

    public Message(string id, object payload)
    {
        Id = id;
        Payload = payload;
    }
}