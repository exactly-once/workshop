using System.Collections.Generic;
using System.Data;
using System.Data.Common;
using System.Data.Entity;
using System.Data.Entity.Infrastructure;
using System.Data.Entity.Validation;
using System.Data.SqlClient;

public class OrdersDataContext :
    DbContext
{
    public OrdersDataContext(IDbConnection connection)
        : base((DbConnection)connection, (bool) false)
    {
    }

    public OrdersDataContext()
    : this(new SqlConnection(Program.ConnectionString))
    {

    }

    public DbSet<Order> Orders { get; set; }
    public DbSet<OrderLine> OrderLines { get; set; }
    protected override void OnModelCreating(DbModelBuilder modelBuilder)
    {
        base.OnModelCreating(modelBuilder);

        var orders = modelBuilder.Entity<Order>();
        orders.ToTable("Orders");
        orders.HasKey(x => x.OrderId);
        orders.HasMany(x => x.Lines).WithRequired().HasForeignKey(x => x.OrderId).WillCascadeOnDelete();

        var lines = modelBuilder.Entity<OrderLine>();
        lines.ToTable("OrderLines");
        lines.HasKey(x => x.Id);
        lines.Property(x => x.Filling);
    }
}