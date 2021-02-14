### Exercise 17: Integrating with Azure Functions

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

Any code executing in the `Once` method will be logically deduplicated and will produce deterministic results in this case `StartNewGame` message.