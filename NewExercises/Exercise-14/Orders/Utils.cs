﻿using System;
using System.Security.Cryptography;
using System.Text;

/// <summary>
/// Based on http://code.logos.com/blog/2011/04/generating_a_deterministic_guid.html
/// </summary>
public static class Utils
{
    public static Guid DeterministicGuid(string previousMessageId, string suffix)
    {
        // convert the name to a sequence of octets (as defined by the standard or conventions of its namespace) (step 3)
        // ASSUME: UTF-8 encoding is always appropriate
        byte[] nameBytes = Encoding.UTF8.GetBytes(suffix);

        // convert the namespace UUID to network order (step 3)
        byte[] namespaceBytes = Encoding.UTF8.GetBytes(previousMessageId);

        // comput the hash of the name space ID concatenated with the name (step 4)
        byte[] hash;
        using (HashAlgorithm algorithm = SHA1.Create())
        {
            algorithm.TransformBlock(namespaceBytes, 0, namespaceBytes.Length, null, 0);
            algorithm.TransformFinalBlock(nameBytes, 0, nameBytes.Length);
            hash = algorithm.Hash;
        }

        // most bytes from the hash are copied straight to the bytes of the new GUID (steps 5-7, 9, 11-12)
        byte[] newGuid = new byte[16];
        Array.Copy(hash, 0, newGuid, 0, 16);

        // set the four most significant bits (bits 12 through 15) of the time_hi_and_version field to the appropriate 4-bit version number from Section 4.1.3 (step 8)
        newGuid[6] = (byte)((newGuid[6] & 0x0F) | (5 << 4));

        // set the two most significant bits (bits 6 and 7) of the clock_seq_hi_and_reserved to zero and one, respectively (step 10)
        newGuid[8] = (byte)((newGuid[8] & 0x3F) | 0x80);

        // convert the resulting UUID to local byte order (step 13)
        SwapByteOrder(newGuid);
        return new Guid(newGuid);
    }

    static void SwapByteOrder(byte[] guid)
    {
        SwapBytes(guid, 0, 3);
        SwapBytes(guid, 1, 2);
        SwapBytes(guid, 4, 5);
        SwapBytes(guid, 6, 7);
    }

    static void SwapBytes(byte[] guid, int left, int right)
    {
        byte temp = guid[left];
        guid[left] = guid[right];
        guid[right] = temp;
    }
}