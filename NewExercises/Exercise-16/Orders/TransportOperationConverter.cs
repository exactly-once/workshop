using System;
using System.Collections.Generic;
using System.Linq;
using NServiceBus;
using NServiceBus.DelayedDelivery;
using NServiceBus.DeliveryConstraints;
using NServiceBus.Performance.TimeToBeReceived;
using NServiceBus.Routing;
using NServiceBus.Transport;
using TransportOperation = NServiceBus.Outbox.TransportOperation;

public static class TransportOperationConverter
{
    public static NServiceBus.Transport.TransportOperation[] Deserialize(this TransportOperation[] operations)
    {
        return operations.Select(o =>
        {
            var message = new OutgoingMessage(o.MessageId, o.Headers, o.Body);
            return new NServiceBus.Transport.TransportOperation(
                message, DeserializeRoutingStrategy(o.Options), o.Options, DispatchConsistency.Isolated);
        }).ToArray();
    }

    public static TransportOperation[] Serialize(this NServiceBus.Transport.TransportOperation[] operations)
    {
        return operations.Select(operation =>
        {
            var dispatchProperties = new DispatchProperties();

            SerializeRoutingStrategy(operation.AddressTag, dispatchProperties);

            return new TransportOperation(operation.Message.MessageId, dispatchProperties, operation.Message.Body, operation.Message.Headers);
        }).ToArray();
    }

    static void SerializeRoutingStrategy(AddressTag addressTag, Dictionary<string, string> options)
    {
        if (addressTag is MulticastAddressTag indirect)
        {
            options["EventType"] = indirect.MessageType.AssemblyQualifiedName;
            return;
        }

        if (addressTag is UnicastAddressTag direct)
        {
            options["Destination"] = direct.Destination;
            return;
        }

        throw new Exception($"Unknown routing strategy {addressTag.GetType().FullName}");
    }

    static AddressTag DeserializeRoutingStrategy(Dictionary<string, string> options)
    {
        if (options.TryGetValue("Destination", out var destination))
        {
            return new UnicastAddressTag(destination);
        }

        if (options.TryGetValue("EventType", out var eventType))
        {
            return new MulticastAddressTag(Type.GetType(eventType, true));
        }

        throw new Exception("Could not find routing strategy to deserialize");
    }
}