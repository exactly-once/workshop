### Prerequisites

- [CosmosDB Emulator](https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-develop-emulator?tabs=docker-linux%2Ccsharp&pivots=api-nosql#install-the-emulator)
- [VisualStudio Code](https://code.visualstudio.com/) with [REST Client extension](https://marketplace.visualstudio.com/items?itemName=humao.rest-client)

### Azure Functions Case Study

In this exercise, we are going to see how to use the algorithm from the previous exercise in the Azure Functions programing model.

The algorithm we already know from the previous parts of the workshop has been implemented in the `ExactlyOnceProcessor` class. The processor is configured via extension mechanism provided by the host in the `HostStartup` class. The functions in turn are passed an instance of the processor as one of the method arguments. The code executing in the processor is a logical equivalent of the code previously implemented in the handlers.

```csharp
[FunctionName(nameof(StartNewGame))]
public async Task<IActionResult> StartNewGame(
    [HttpTrigger(AuthorizationLevel.Anonymous, "post")] StartNewGameReques request,
    [ExactlyOnce("{gameId}")] IOnceExecutor execute,
    [Queue("start-game")] ICollector<StartNewGame> collector,
    ILogger log)
{
    log.LogInformation($"Processing StartNewGame: gameId={request.GameId}");

    var startNewGame = await execute.Once(
        () => new StartNewGame
        {
            GameId = request.GameId.ToGuid()
        }
    );

    collector.Add(startNewGame);

    return new AcceptedResult();
}
```

Any code executing in the `Once` method is deduplicated and produces deterministic results - in the example above a `StartNewGame` message.


### Exercise 


> **_NOTE:_** Use the [requests.http](./requests.http) to trigger http requests to our functions app.

* We would like to extend our sample application by storing the game leader board in Azure blob whenever a game ends.
* Let's start by adding new `SaveLeaderBoard` command
```csharp
    public class SaveLeaderBoard
    {
        public Guid GameId { get; set; }
    }
```
* Make sure that ending the game (in `ShootingRange.cs`) results in sending out the `SaveLeaderBoard` command
```csharp
[FunctionName(nameof(HandleEndGame))]
public async Task HandleEndGame(
    [QueueTrigger("end-game")] EndGame endGame,
    [ExactlyOnce("{requestId}", "{gameId}")] IOnceExecutor<ShootingRangeState> execute,
    [Queue("save-leader-board")] ICollector<SaveLeaderBoard> collector,
    ILogger log)
{
    log.LogWarning($"Processed endGame:gameId={endGame.GameId}");

    var saveLeaderBoard = await execute.Once(sr =>
    {
        sr.IsActive = false;

        return new SaveLeaderBoard {GameId = endGame.GameId};
    });

    collector.Add(saveLeaderBoard);
}
```
* Now lets add new function in the `LeaderBoard.cs` to handle the command and save the blob
```csharp
[FunctionName(nameof(SaveLeaderBoard))]
public async Task SaveLeaderBoard(
    [QueueTrigger("save-leader-board")] SaveLeaderBoard saveLeaderBoard,
    [ExactlyOnce(requestId: "{gameId}", stateId: "{gameId}")] IOnceExecutor<LeaderBoardState> execute,
    [Blob("game-results/{gameId}", FileAccess.Write)] TextWriter gameResultsBlob,
    ILogger log)
{
    log.LogWarning($"Processing save leader board : gameId={saveLeaderBoard.GameId}");

    var results = await execute.Once<GameResults>(board => new GameResults
    {
        EndDate = DateTime.Now,
        Hits = board.NumberOfHits,
        Misses = board.NumberOfAttempts - board.NumberOfHits
    });

    await gameResultsBlob.WriteLineAsync(@$"Date={results.EndDate}, Hits={results.Hits}, Misses={results.Misses}");
}
```
* The exactly once processor returns an intance of `GameResults` class that has to be defined
```csharp
public class GameResults
{
    public DateTime EndDate { get; set; }
    public int Hits { get; set; }
    public int Misses { get; set; }
}
```
