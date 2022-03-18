using Messages;

public class OrderLine
{
    public Filling Filling { get; set; }

    public OrderLine(Filling filling)
    {
        Filling = filling;
    }
}