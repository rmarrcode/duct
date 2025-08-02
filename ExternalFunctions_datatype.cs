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
    
    public static Dafny.ISequence<YamlToDatatypeTranslator._ITable> ParseYaml(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> lines) {
        try {
            Console.WriteLine($"ParseYaml called with {lines.Count} lines");
            
            // Convert Dafny sequences to C# strings
            var stringLines = new List<string>();
            for (int i = 0; i < lines.Count; i++) {
                string line = string.Join("", lines.CloneAsArray()[i].Select(r => r.ToString()));
                stringLines.Add(line);
                Console.WriteLine($"Line {i}: '{line}'");
            }
            
            var tables = new List<YamlToDatatypeTranslator._ITable>();
            var currentTable = (YamlToDatatypeTranslator._ITable)null;
            var currentColumns = new List<YamlToDatatypeTranslator._IColumn>();
            
            for (int i = 0; i < stringLines.Count; i++) {
                string line = stringLines[i].TrimEnd();
                
                // Skip empty lines
                if (string.IsNullOrWhiteSpace(line)) {
                    continue;
                }
                
                Console.WriteLine($"Processing line: '{line}'");
                
                // Check if this is a table entry (starts with "- name:" after trimming)
                if (line.TrimStart().StartsWith("- name:")) {
                    Console.WriteLine($"Found table entry: {line}");
                    // Save previous table if exists
                    if (currentTable != null) {
                        // Create new table with current columns
                        currentTable = YamlToDatatypeTranslator.Table.create(
                            currentTable.dtor_name,
                            Dafny.Sequence<YamlToDatatypeTranslator._IColumn>.FromElements(currentColumns.ToArray())
                        );
                        tables.Add(currentTable);
                    }
                    
                    // Start new table
                    string tableName = line.TrimStart().Substring("- name:".Length).Trim();
                    currentTable = YamlToDatatypeTranslator.Table.create(
                        Dafny.Sequence<Dafny.Rune>.UnicodeFromString(tableName),
                        Dafny.Sequence<YamlToDatatypeTranslator._IColumn>.Empty
                    );
                    currentColumns.Clear();
                }
                // Check if this is a columns section
                else if (line.TrimStart().StartsWith("columns:")) {
                    Console.WriteLine($"Found columns section: {line}");
                    // Columns section started, continue to next line
                    continue;
                }
                // Check if this is a column entry (starts with "- name:" after trimming)
                else if (line.TrimStart().StartsWith("- name:") && currentTable != null) {
                    Console.WriteLine($"Found column entry: {line}");
                    string columnName = line.TrimStart().Substring("- name:".Length).Trim();
                    
                    // Look for the type on the next line
                    if (i + 1 < stringLines.Count) {
                        string nextLine = stringLines[i + 1].TrimEnd();
                        if (nextLine.TrimStart().StartsWith("type:")) {
                            string columnType = nextLine.TrimStart().Substring("type:".Length).Trim();
                            Console.WriteLine($"Found column type: {columnType} for {columnName}");
                            currentColumns.Add(YamlToDatatypeTranslator.Column.create(
                                Dafny.Sequence<Dafny.Rune>.UnicodeFromString(columnName),
                                Dafny.Sequence<Dafny.Rune>.UnicodeFromString(columnType)
                            ));
                            i++; // Skip the type line since we've processed it
                        }
                    }
                }
            }
            
            // Add the last table if exists
            if (currentTable != null) {
                currentTable = YamlToDatatypeTranslator.Table.create(
                    currentTable.dtor_name,
                    Dafny.Sequence<YamlToDatatypeTranslator._IColumn>.FromElements(currentColumns.ToArray())
                );
                tables.Add(currentTable);
            }
            
            Console.WriteLine($"Parsed {tables.Count} tables");
            return Dafny.Sequence<YamlToDatatypeTranslator._ITable>.FromElements(tables.ToArray());
        }
        catch (Exception ex) {
            Console.Error.WriteLine($"Error parsing YAML: {ex.Message}");
            return Dafny.Sequence<YamlToDatatypeTranslator._ITable>.FromElements();
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