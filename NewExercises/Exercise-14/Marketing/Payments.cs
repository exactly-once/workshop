using System.Collections.Generic;
using NServiceBus;

namespace Marketing
{
    public class Payments : Entity
    {
        public int TotalValue { get; set; }
        public List<string> ProcessedMessage = new List<string>();
        public List<ICommand> OutgoingMessages = new List<ICommand>();

        public static string RowId = "39D0410D-02C2-49B9-BDC7-9A66EDEB456D";
    }
}