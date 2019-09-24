using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;

public class Order
{
    public Order()
    {
        Lines = new List<OrderLine>();
    }

    [MaxLength(20)]
    public string OrderId { get; set; }
    public virtual ICollection<OrderLine> Lines { get; set; }
}