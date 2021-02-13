using System.Collections.Generic;
using Messages;

public class ShoppingCart : Entity
{
    public bool Submitted { get; set; }
    public List<Filling> Items = new List<Filling>();
}