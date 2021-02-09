using Messages;

public class Order : IEntity
{
    public object VersionInfo { get; set; }
    public string Id { get; set; }
    public Filling Filling { get; set; }
}