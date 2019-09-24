using System.Data.SqlClient;

public static class SqlHelper
{
    public static void EnsureDatabaseExists(string connectionString)
    {
        var builder = new SqlConnectionStringBuilder(connectionString);
        var database = builder.InitialCatalog;

        var masterConnection = connectionString.Replace(builder.InitialCatalog, "master");

        using (var connection = new SqlConnection(masterConnection))
        {
            connection.Open();

            using (var command = connection.CreateCommand())
            {
                command.CommandText = $@"
if(db_id('{database}') is not null)
begin
    alter database [{database}] set single_user with rollback immediate;
    drop database [{database}];
end
create database [{database}];
";
                command.ExecuteNonQuery();
            }
        }
    }
}