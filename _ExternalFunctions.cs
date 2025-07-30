using System;
using System.IO;
using System.Collections.Generic;

public class ExternalFunctions {
    
    public static List<Table> ParseYaml(List<string> lines) {
        try {
        // Simple implementation for now - just return empty list
        // TODO: Implement proper YAML parsing
        Console.WriteLine("ParseYaml called with " + lines.Count + " lines");
        return new List<Table>();
        }
        catch (Exception ex) {
        Console.Error.WriteLine($"Error parsing YAML: {ex.Message}");
        return new List<Table>();
        }
    }

    public static List<string> ReadAllLines(string path) {
        try {
        return new List<string>(File.ReadAllLines(path));
        }
        catch (Exception ex) {
        Console.Error.WriteLine($"Error reading file: {ex.Message}");
        return new List<string>();
        }
    }

    public static void WriteLine(string s) {
        Console.WriteLine(s);
    }
}
