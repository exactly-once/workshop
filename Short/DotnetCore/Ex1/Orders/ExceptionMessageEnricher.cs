using System;
using Serilog.Core;
using Serilog.Events;

class ExceptionMessageEnricher : ILogEventEnricher
{
    public void Enrich(LogEvent logEvent, ILogEventPropertyFactory propertyFactory)
    {
        if (logEvent.Exception != null)
        {
            logEvent.AddOrUpdateProperty(new LogEventProperty("ExceptionMessage", new ScalarValue(ExceptionWithoutStackTrace(logEvent.Exception))));
        }
    }

    string ExceptionWithoutStackTrace(Exception rootException)
    {
        if (rootException.InnerException != null)
        {
            return ExceptionWithoutStackTrace(rootException.InnerException);
        }
        return rootException.Message;
    }
}