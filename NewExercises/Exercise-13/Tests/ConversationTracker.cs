using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Messaging.IntegrationTests.Tests
{
    public class ConversationTracker
    {
        ConcurrentDictionary<Guid, ConversationState> conversations =
            new ConcurrentDictionary<Guid, ConversationState>();

        public void UpdateConversations(TraceMessage trace)
        {
            var conversationId = trace.ConversationId;
            var processedMessageId = trace.IncomingMessageId;
            var inflightMessageIds = trace.OutgoingMessageId;

            if (conversations.ContainsKey(conversationId) == false)
            {
                return;
            }

            conversations.AddOrUpdate(
                conversationId,
                id => throw new Exception("Invalid conversation tracking state."),
                (id, s) => s.Update(processedMessageId, inflightMessageIds));
        }

        public Task WaitForConversationToFinish(Guid conversationId)
        {
            return conversations[conversationId].CompletionSource.Task;
        }

        public void SetupConversationTracking(Guid conversationId, Guid firstMessageId)
        {
            var added = conversations.TryAdd(conversationId, new ConversationState(firstMessageId));

            if (added == false)
            {
                throw new Exception($"Failed to setup conversation tracking for {conversationId}.");
            }
        }

        class ConversationState
        {
            Dictionary<Guid, bool> processed = new Dictionary<Guid, bool>();

            public TaskCompletionSource<bool> CompletionSource { get; } = new TaskCompletionSource<bool>();

            public ConversationState(Guid firstMessageId)
            {
                AddIfNotInProcessed(firstMessageId);
            }

            public ConversationState Update(Guid processedId, Guid[] inFlightIds)
            {
                AddIfNotInProcessed(processedId);

                processed[processedId] = true;

                inFlightIds.ToList().ForEach(AddIfNotInProcessed);

                if (processed.All(kv => kv.Value))
                {
                    CompletionSource.SetResult(true);
                }

                return this;
            }

            void AddIfNotInProcessed(Guid id)
            {
                if (processed.ContainsKey(id) == false)
                {
                    processed.Add(id, false);
                }
            }
        }
    }
}