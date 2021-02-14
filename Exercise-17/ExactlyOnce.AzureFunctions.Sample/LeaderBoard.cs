using System.Threading.Tasks;
using Microsoft.Azure.WebJobs;
using Microsoft.Extensions.Logging;
using Newtonsoft.Json;

namespace ExactlyOnce.AzureFunctions.Sample
{
    public class LeaderBoard
    {
        [FunctionName(nameof(UpdateLeaderBoard))]
        public async Task UpdateLeaderBoard(
            [QueueTrigger("attempt-updates")] AttemptMade attempt, 
            [ExactlyOnce(requestId: "{attemptId}", stateId: "{gameId}")] IOnceExecutor<LeaderBoardState> execute,
            ILogger log)
        {
            log.LogInformation($"Processing attempt result: gameId={attempt.GameId}, isHit={attempt.IsHit}");

            await execute.Once(board =>
                {
                    board.NumberOfAttempts++;

                    if (attempt.IsHit)
                    {
                        board.NumberOfHits++;
                    }
                });
        }

        public class LeaderBoardState : State
        {
            [JsonProperty("numberOfAttempts")] public int NumberOfAttempts { get; set; }

            [JsonProperty("numberOfHits")] public int NumberOfHits { get; set; }
        }
    }
}