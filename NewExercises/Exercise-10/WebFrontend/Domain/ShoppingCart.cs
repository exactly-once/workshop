using System.Collections.Generic;
using Messages;

public class ShoppingCart : Entity
{
    public List<Filling> Items { get; set; }= new List<Filling>();
    public bool Accepted { get; set; }
    public bool Submitted { get; set; } 
}