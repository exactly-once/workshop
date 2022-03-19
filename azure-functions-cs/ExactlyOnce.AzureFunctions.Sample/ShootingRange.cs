using System;
using System.Globalization;
using System.Net.Http;
using System.Threading.Tasks;
using Microsoft.Azure.WebJobs;
using Microsoft.Extensions.Logging;

namespace ExactlyOnce.AzureFunctions.Sample
{
    public class ShootingRange
    {
        static HttpClient httpClient = new HttpClient();

        [FunctionName(nameof(HandleFireAt))]
        [return: Queue("attempt-updates")]
        public async Task<AttemptMade> HandleFireAt(
            [QueueTrigger("fire-at")] FireAt fireAt,
            [ExactlyOnce("{attemptId}", "{gameId}")]
            IOnceExecutor<ShootingRangeState> execute,
            ILogger log)
        {
            var timestamp = await ExecuteHttpRequest();

            var message = await execute.Once(sr =>
            {
                if (sr.IsActive == false)
                {
                    return default;
                }

                var attemptMade = new AttemptMade
                {
                    AttemptId = fireAt.AttemptId,
                    GameId = fireAt.GameId
                };

                if (sr.TargetPosition == fireAt.Position)
                {
                    attemptMade.IsHit = true;
                }
                else
                {
                    attemptMade.IsHit = false;
                }

                attemptMade.Timestamp = timestamp;

                return attemptMade;
            });

            log.LogWarning($"Processed FireAt: gameId={fireAt.GameId}, position={fireAt.Position}, timestamp={message.Timestamp}");

            return message;
        }

        [FunctionName(nameof(HandleNewGame))]
        public async Task HandleNewGame(
            [QueueTrigger("start-game")] StartNewGame startGame,
            [ExactlyOnce("{gameId}", "{gameId}")] IOnceExecutor<ShootingRangeState> execute,
            ILogger log)
        {
            log.LogWarning($"Processed startGame:gameId={startGame.GameId}");

            await execute.Once(sr =>
            {
                sr.IsActive = true;
                sr.TargetPosition = new Random().Next(0, 10);
                sr.NumberOfAttempts = 0;
            });
        }

        [FunctionName(nameof(HandleEndGame))]
        public async Task HandleEndGame(
            [QueueTrigger("end-game")] StartNewGame startGame,
            [ExactlyOnce("{gameId}", "{gameId}")] IOnceExecutor<ShootingRangeState> execute,
            ILogger log)
        {
            log.LogWarning($"Processed endGame:gameId={startGame.GameId}");

            await execute.Once(sr =>
            {
                sr.IsActive = false;
            });
        }

        async Task<DateTime> ExecuteHttpRequest()
        {
            var result = await httpClient.GetAsync("http://localhost:7071/api/RequestTimestamp");

            var content = await result.Content.ReadAsStringAsync();

            return DateTime.Parse(content, CultureInfo.InvariantCulture);
        }

        public class ShootingRangeState : State
        {
            public bool IsActive { get; set; }
            public int TargetPosition { get; set; }
            public int NumberOfAttempts { get; set; }
        }
    }
}