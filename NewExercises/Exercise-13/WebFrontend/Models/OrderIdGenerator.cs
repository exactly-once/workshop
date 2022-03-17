using System;
using System.Linq;

namespace Orders.Models
{
    public class OrderIdGenerator
    {
        const string letters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        static readonly Random r = new Random();

        public static string Generate()
        {
            return new string(Enumerable.Range(0, 4).Select(i => letters[r.Next(letters.Length)]).ToArray());
        }
    }
}