using System;

namespace ExactlyOnce.AzureFunctions.Sample
{
    public class FireAt
    {
        public Guid AttemptId { get; set; }
        public Guid GameId { get; set; }
        public int Position { get; set; }
    }

    public class StartNewGame
    {
        public Guid GameId { get; set; }
    }

    public class EndGame
    {
        public Guid GameId { get; set; }
    }

    public class AttemptMade
    {
        public Guid AttemptId { get; set; }
        public bool IsHit { get; set; }
        public Guid GameId { get; set; }
        public DateTime Timestamp { get; set; }
    }

    public class GameFinished
    {
        public Guid GameId { get; set; }
    }

    public class BlobInfo
    {
        public string BlobName { get; set; }
    }
}