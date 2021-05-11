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
                message,
                DeserializeRoutingStrategy(o.Options),
                DispatchConsistency.Isolated,
                DeserializeConstraints(o.Options));
        }).ToArray();
    }

    public static TransportOperation[] Serialize(this NServiceBus.Transport.TransportOperation[] operations)
    {
        return operations.Select(operation =>
        {
            var options = new Dictionary<string, string>();

            foreach (var constraint in operation.DeliveryConstraints)
            {
                SerializeDeliveryConstraint(constraint, options);
            }

            SerializeRoutingStrategy(operation.AddressTag, options);

            return new TransportOperation(operation.Message.MessageId, options, operation.Message.Body, operation.Message.Headers);
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

    static void SerializeDeliveryConstraint(DeliveryConstraint constraint, Dictionary<string, string> options)
    {
        if (constraint is NonDurableDelivery)
        {
            options["NonDurable"] = true.ToString();
            return;
        }
        if (constraint is DoNotDeliverBefore doNotDeliverBefore)
        {
            options["DeliverAt"] = DateTimeExtensions.ToWireFormattedString(doNotDeliverBefore.At);
            return;
        }

        if (constraint is DelayDeliveryWith delayDeliveryWith)
        {
            options["DelayDeliveryFor"] = delayDeliveryWith.Delay.ToString();
            return;
        }

        if (constraint is DiscardIfNotReceivedBefore discard)
        {
            options["TimeToBeReceived"] = discard.MaxTime.ToString();
            return;
        }

        throw new Exception($"Unknown delivery constraint {constraint.GetType().FullName}");
    }

    static List<DeliveryConstraint> DeserializeConstraints(Dictionary<string, string> options)
    {
        var constraints = new List<DeliveryConstraint>(4);
        if (options.ContainsKey("NonDurable"))
        {
            constraints.Add(new NonDurableDelivery());
        }

        if (options.TryGetValue("DeliverAt", out var deliverAt))
        {
            constraints.Add(new DoNotDeliverBefore(DateTimeExtensions.ToUtcDateTime(deliverAt)));
        }

        if (options.TryGetValue("DelayDeliveryFor", out var delay))
        {
            constraints.Add(new DelayDeliveryWith(TimeSpan.Parse(delay)));
        }

        if (options.TryGetValue("TimeToBeReceived", out var ttbr))
        {
            constraints.Add(new DiscardIfNotReceivedBefore(TimeSpan.Parse(ttbr)));
        }
        return constraints;
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