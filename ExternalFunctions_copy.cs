using System;
using System.IO;
using System.Collections.Generic;

public class ExternalFunctions {
    
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ReadAllLines(Dafny.ISequence<Dafny.Rune> path) {
        try {
            // Convert Dafny sequence of runes to string by joining characters
            string filePath = string.Join("", path.Select(r => r.ToString()));
            Console.WriteLine($"ReadAllLines called with path: {filePath}");
            string[] lines = File.ReadAllLines(filePath);
            Console.WriteLine($"Read {lines.Length} lines from file");
            
            var result = new List<Dafny.ISequence<Dafny.Rune>>();
            foreach (string line in lines) {
                result.Add(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(line));
            }
            return Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(result.ToArray());
        }
        catch (Exception ex) {
            Console.Error.WriteLine($"Error reading file: {ex.Message}");
            return Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
    }
    
}
