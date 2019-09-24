using System;
using Messages;

public class OrderLine
{
    public Guid Id { get; set; } = Guid.NewGuid();
    public Filling Filling { get; set; }
    public string OrderId { get; set; }

    public OrderLine()
    {

    }

    public OrderLine(Filling filling)
    {
        Filling = filling;
    }
}