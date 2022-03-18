using System;
using System.Collections.Generic;
using Messages;

public class Order : Entity
{
    public List<Filling> Items { get; set; }= new List<Filling>();

    public bool PaymentBooked { get; set; }

    public int Value { get; set; }

    public List<Guid> ProcessedMessages = new List<Guid>();

}