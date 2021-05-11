public class Message
{
    public string Id { get; set; }
    public string Payload { get; set; }

    public Message()
    {
    }

    public Message(string id, string payload)
    {
        Id = id;
        Payload = payload;
    }
}