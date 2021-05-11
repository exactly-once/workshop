using System.Collections.Generic;

public class OutboxState
{
    public List<Message> OutgoingMessages { get; set; } = new List<Message>()
}