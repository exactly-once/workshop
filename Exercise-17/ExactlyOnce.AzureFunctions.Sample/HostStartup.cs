using System;
using ExactlyOnce.AzureFunctions.Sample;
using Microsoft.Azure.Cosmos;
using Microsoft.Azure.WebJobs;
using Microsoft.Azure.WebJobs.Hosting;

[assembly: WebJobsStartup(typeof(HostStartup))]

namespace ExactlyOnce.AzureFunctions.Sample
{
    public class HostStartup : IWebJobsStartup
    {
        public void Configure(IWebJobsBuilder builder)
        {
            builder.AddExactlyOnce(c =>
            {
                c.ConfigureOutbox(o =>
                {
                    o.DatabaseId = "E1Sandbox";
                    o.ContainerId = "Outbox";
                    o.RetentionPeriod = TimeSpan.FromDays(1);
                });

                c.UseCosmosClient(() =>
                {
                    //Emulator credentials
                    var endpointUri = "https://localhost:8081";
                    var primaryKey = "C2y6yDjf5/R+ob0N8A7Cgv30VRDJIWEHLM+4QDU5DE2nQ9nDuVTqobD4b8mGGyPMbIZnqyMsEcaGQy67XIw/Jw==";

                    return new CosmosClient(endpointUri, primaryKey);
                });
            });
        }
    }
}