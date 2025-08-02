using System;
using System.IO;
using System.Collections.Generic;
using System.Linq;

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
    
    public static Dafny.ISequence<YamlToRowDatatypeTranslator._IRow> ParseDataYaml(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> lines) {
        try {
            Console.WriteLine($"ParseDataYaml called with {lines.Count} lines");
            
            // Convert Dafny sequences to C# strings
            var stringLines = new List<string>();
            for (int i = 0; i < lines.Count; i++) {
                string line = string.Join("", lines.CloneAsArray()[i].Select(r => r.ToString()));
                stringLines.Add(line);
                Console.WriteLine($"Data Line {i}: '{line}'");
            }
            
            var rows = new List<YamlToRowDatatypeTranslator._IRow>();
            var currentTableName = "";
            
            for (int i = 0; i < stringLines.Count; i++) {
                string line = stringLines[i].TrimEnd();
                
                // Skip empty lines
                if (string.IsNullOrWhiteSpace(line)) {
                    continue;
                }
                
                Console.WriteLine($"Processing data line: '{line}'");
                
                // Check if this is a table name (e.g., "users:")
                if (line.TrimStart().EndsWith(":") && !line.TrimStart().StartsWith("-")) {
                    currentTableName = line.TrimStart().TrimEnd(':');
                    Console.WriteLine($"Found table: {currentTableName}");
                    continue;
                }
                
                // Check if this is a data row (starts with "- ")
                if (line.TrimStart().StartsWith("- ")) {
                    Console.WriteLine($"Found data row: {line}");
                    
                    // Parse the values from the row
                    string rowData = line.TrimStart().Substring("- ".Length);
                    var values = new List<string>();
                    
                    // Simple parsing: split by commas
                    string[] parts = rowData.Split(',');
                    foreach (string part in parts) {
                        string trimmed = part.Trim();
                        if (!string.IsNullOrEmpty(trimmed)) {
                            values.Add(trimmed);
                        }
                    }
                    
                    if (values.Count > 0) {
                        var rowValues = new List<Dafny.ISequence<Dafny.Rune>>();
                        foreach (string value in values) {
                            rowValues.Add(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(value));
                        }
                        
                        rows.Add(YamlToRowDatatypeTranslator.Row.create(
                            Dafny.Sequence<Dafny.Rune>.UnicodeFromString(currentTableName),
                            Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(rowValues.ToArray())
                        ));
                    }
                }
            }
            
            Console.WriteLine($"Parsed {rows.Count} data rows");
            return Dafny.Sequence<YamlToRowDatatypeTranslator._IRow>.FromElements(rows.ToArray());
        }
        catch (Exception ex) {
            Console.Error.WriteLine($"Error parsing data YAML: {ex.Message}");
            return Dafny.Sequence<YamlToRowDatatypeTranslator._IRow>.FromElements();
        }
    }
    
    public static void WriteLine(Dafny.ISequence<Dafny.Rune> s) {
        try {
            string output = string.Join("", s.Select(r => r.ToString()));
            Console.WriteLine(output);
        }
        catch (Exception ex) {
            Console.Error.WriteLine($"Error writing line: {ex.Message}");
        }
    }
} 