using System.Collections.Generic;

public class ShoppingCart : Entity
{
    public List<Filling> Items { get; set; }= new List<Filling>();
    public bool Submitted { get; set; } 
}