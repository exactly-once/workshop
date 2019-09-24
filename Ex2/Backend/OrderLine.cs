using System;
using System.ComponentModel.DataAnnotations.Schema;
using Messages;

public class OrderLine
{
    public Guid Id { get; set; } = Guid.NewGuid();
    [Index("IX_UniqueLine", 1, IsUnique = true)]
    public Filling Filling { get; set; }
    [Index("IX_UniqueLine", 2, IsUnique = true)]
    public string OrderId { get; set; }

    public OrderLine()
    {

    }

    public OrderLine(Filling filling)
    {
        Filling = filling;
    }
}