using System.Collections.Generic;

public class Order : Entity
{
    public List<Filling> Items = new List<Filling>();
}