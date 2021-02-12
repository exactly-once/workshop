using NServiceBus.Outbox;

public class OutboxState
{
    public TransportOperation[] OutgoingMessages { get; set; }
    public bool TokensGenerated { get; set; }
}