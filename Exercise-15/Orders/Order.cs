using System.Collections.Generic;

public class Order : Entity
{
    public List<OrderLine> Lines { get; set; } = new List<OrderLine>();
}