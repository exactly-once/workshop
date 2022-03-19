using System;
using System.Globalization;
using System.Threading.Tasks;
using Microsoft.AspNetCore.Http;
using Microsoft.AspNetCore.Mvc;
using Microsoft.Azure.WebJobs;
using Microsoft.Azure.WebJobs.Extensions.Http;
using Microsoft.Extensions.Logging;

namespace ExactlyOnce.AzureFunctions.Sample
{
    public class ExternalApi
    {
        [FunctionName(nameof(RequestTimestamp))]
        public async Task<IActionResult> RequestTimestamp(
            [HttpTrigger(AuthorizationLevel.Anonymous, "get")]HttpRequest req,
            ILogger log)
        {
            var timestamp = DateTime.UtcNow;

            log.LogWarning($"Timestamp generated: {timestamp}");

            return new ContentResult
            {
                Content = timestamp.ToString(CultureInfo.InvariantCulture)
            };
        }
    }
}