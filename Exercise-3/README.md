# Exercise 3: Message duplication on the sender side

In this exercise we are going to experience message duplication again. This time our task is to build a piece of code that imports *pierogi* orders from an external system. Fortunately that system supports only one item per order.

The console accepts commands in form of `submit <order-id> with <filling>`. Each such command stores a record in the database. Every two seconds all existing records are loaded and passed to import method (the `Importer` class. There is an error handling mechanism built-in that catches all import exceptions and prints them to the console.

The import logic is supposed to send two commands for each record from the database:
 - `SubmitOrder`
 - `AddItem`

How can we make sure the same order is not processed multiple times?