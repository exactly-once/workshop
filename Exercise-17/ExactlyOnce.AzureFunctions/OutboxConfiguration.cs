using System;

namespace ExactlyOnce.AzureFunctions
{
    public class OutboxConfiguration
    {
        public string DatabaseId { get; set; }
        public string ContainerId { get; set; } = "Outbox";
        public TimeSpan RetentionPeriod { get; set; }

        public void Validate()
        {
            if (string.IsNullOrEmpty(DatabaseId))
            {
                throw new ArgumentOutOfRangeException(nameof(DatabaseId), DatabaseId);
            }

            if (string.IsNullOrEmpty(ContainerId))
            {
                throw new ArgumentOutOfRangeException(nameof(ContainerId), ContainerId);
            }

            if (RetentionPeriod == default)
            {
                throw new ArgumentOutOfRangeException(nameof(RetentionPeriod), $"Outbox {RetentionPeriod} has to be explicitly specified.");
            }
        }
    }
}