using System.Threading.Tasks;
using Microsoft.AspNetCore.Mvc;
using Microsoft.Azure.WebJobs;
using Microsoft.Azure.WebJobs.Extensions.Http;
using Microsoft.Extensions.Logging;

namespace ExactlyOnce.AzureFunctions.Sample
{
    public class HttpApi
    {
        [FunctionName(nameof(FireAt))]
        public async Task<IActionResult> FireAt(
            [HttpTrigger(AuthorizationLevel.Anonymous, "post")] FireAtRequest request,
            [ExactlyOnce("{requestId}")] IOnceExecutor execute,
            [Queue("fire-at")] ICollector<FireAt> collector,
            ILogger log)
        {
            log.LogWarning($"Processing FireAt: requestId={request.RequestId}");

            var fireAt = await execute.Once(
                () => new FireAt
                {
                    AttemptId = request.RequestId.ToGuid(),
                    GameId = request.GameId.ToGuid(),
                    Position = request.Position
                }
            );

            collector.Add(fireAt);

            return new AcceptedResult();
        }

        [FunctionName(nameof(StartNewGame))]
        public async Task<IActionResult> StartNewGame(
            [HttpTrigger(AuthorizationLevel.Anonymous, "post")]
            StartNewGameRequest request,
            [ExactlyOnce("{gameId}")] IOnceExecutor execute,
            [Queue("start-game")] ICollector<StartNewGame> collector,
            ILogger log)
        {
            log.LogWarning($"Processing StartNewGame: gameId={request.GameId}");

            var startNewGame = await execute.Once(
                () => new StartNewGame
                {
                    //TODO: add timestamp field
                    GameId = request.GameId.ToGuid()
                }
            );

            collector.Add(startNewGame);

            return new AcceptedResult();
        }

        [FunctionName(nameof(EndGame))]
        public async Task<IActionResult> EndGame(
            [HttpTrigger(AuthorizationLevel.Anonymous, "post")]
            EndGameRequest request,
            [ExactlyOnce("{gameId}")] IOnceExecutor execute,
            [Queue("end-game")] ICollector<EndGame> collector,
            ILogger log)
        {
            log.LogWarning($"Processing EndGame: gameId={request.GameId}");

            var endGame = await execute.Once(
                () => new EndGame
                {
                    GameId = request.GameId.ToGuid()
                }
            );

            collector.Add(endGame);

            return new AcceptedResult();
        }

        public class StartNewGameRequest
        {
            public string GameId { get; set; }
        }

        public class FireAtRequest
        {
            public string RequestId { get; set; }
            public string GameId {get; set; }
            public int Position {get; set; }
        }

        public class EndGameRequest
        {
            public string GameId { get; set; }
        }
    }
}