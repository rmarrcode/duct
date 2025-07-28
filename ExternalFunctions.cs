using System;
using System.IO;
using System.Collections.Generic;
using System.Numerics;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;

namespace YamlToDafnyTranslator
{
    // Extension methods to provide external function implementations
    public static class ExternalFunctions
    {
        // Implementation of ReadAllLines external function
        public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ReadAllLines(Dafny.ISequence<Dafny.Rune> path)
        {
            try
            {
                string filePath = path.ToString();
                string[] lines = File.ReadAllLines(filePath);
                
                var result = new List<Dafny.ISequence<Dafny.Rune>>();
                foreach (string line in lines)
                {
                    result.Add(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(line));
                }
                
                return Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(result.ToArray());
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine($"Error reading file: {ex.Message}");
                return Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty;
            }
        }

        // Implementation of WriteLine external function
        public static void WriteLine(Dafny.ISequence<Dafny.Rune> s)
        {
            Console.WriteLine(s.ToString());
        }

        // Implementation of ParseYaml external function
        public static Dafny.ISequence<YamlToDafnyTranslator._ITable> ParseYaml(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> lines)
        {
            try
            {
                // Convert Dafny sequences to string for YAML parsing
                string yamlContent = "";
                for (int i = 0; i < lines.Count; i++)
                {
                    yamlContent += lines.Select(new BigInteger(i)).ToString() + "\n";
                }

                var tables = new List<YamlToDafnyTranslator._ITable>();
                
                using (var reader = new StringReader(yamlContent))
                using (var yamlReader = new Parser(reader))
                {
                    yamlReader.Consume<StreamStart>();
                    
                    while (yamlReader.Current != null && !yamlReader.Current.GetType().Equals(typeof(StreamEnd)))
                    {
                        if (yamlReader.Current is MappingStart)
                        {
                            yamlReader.Consume<MappingStart>();
                            
                            while (yamlReader.Current != null && !yamlReader.Current.GetType().Equals(typeof(MappingEnd)))
                            {
                                if (yamlReader.Current is Scalar scalar && scalar.Value == "tables")
                                {
                                    yamlReader.Consume<Scalar>();
                                    
                                    if (yamlReader.Current is SequenceStart)
                                    {
                                        yamlReader.Consume<SequenceStart>();
                                        
                                        while (yamlReader.Current != null && !yamlReader.Current.GetType().Equals(typeof(SequenceEnd)))
                                        {
                                            if (yamlReader.Current is MappingStart)
                                            {
                                                var table = ParseTable(yamlReader);
                                                if (table != null)
                                                {
                                                    tables.Add(table);
                                                }
                                            }
                                            else
                                            {
                                                yamlReader.Consume();
                                            }
                                        }
                                        
                                        if (yamlReader.Current is SequenceEnd)
                                        {
                                            yamlReader.Consume<SequenceEnd>();
                                        }
                                    }
                                }
                                else
                                {
                                    yamlReader.Consume();
                                }
                            }
                            
                            if (yamlReader.Current is MappingEnd)
                            {
                                yamlReader.Consume<MappingEnd>();
                            }
                        }
                        else
                        {
                            yamlReader.Consume();
                        }
                    }
                }
                
                return Dafny.Sequence<YamlToDafnyTranslator._ITable>.FromElements(tables.ToArray());
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine($"Error parsing YAML: {ex.Message}");
                return Dafny.Sequence<YamlToDafnyTranslator._ITable>.Empty;
            }
        }

        private static YamlToDafnyTranslator._ITable ParseTable(Parser yamlReader)
        {
            string tableName = "";
            var columns = new List<YamlToDafnyTranslator._IColumn>();
            
            yamlReader.Consume<MappingStart>();
            
            while (yamlReader.Current != null && !yamlReader.Current.GetType().Equals(typeof(MappingEnd)))
            {
                if (yamlReader.Current is Scalar scalar)
                {
                    string key = scalar.Value;
                    yamlReader.Consume<Scalar>();
                    
                    if (key == "name" && yamlReader.Current is Scalar nameScalar)
                    {
                        tableName = nameScalar.Value;
                        yamlReader.Consume<Scalar>();
                    }
                    else if (key == "columns" && yamlReader.Current is SequenceStart)
                    {
                        yamlReader.Consume<SequenceStart>();
                        
                        while (yamlReader.Current != null && !yamlReader.Current.GetType().Equals(typeof(SequenceEnd)))
                        {
                            if (yamlReader.Current is MappingStart)
                            {
                                var column = ParseColumn(yamlReader);
                                if (column != null)
                                {
                                    columns.Add(column);
                                }
                            }
                            else
                            {
                                yamlReader.Consume();
                            }
                        }
                        
                        if (yamlReader.Current is SequenceEnd)
                        {
                            yamlReader.Consume<SequenceEnd>();
                        }
                    }
                    else
                    {
                        yamlReader.Consume();
                    }
                }
                else
                {
                    yamlReader.Consume();
                }
            }
            
            if (yamlReader.Current is MappingEnd)
            {
                yamlReader.Consume<MappingEnd>();
            }
            
            if (!string.IsNullOrEmpty(tableName))
            {
                return YamlToDafnyTranslator.Table.create(
                    Dafny.Sequence<Dafny.Rune>.UnicodeFromString(tableName),
                    Dafny.Sequence<YamlToDafnyTranslator._IColumn>.FromElements(columns.ToArray())
                );
            }
            
            return null;
        }

        private static YamlToDafnyTranslator._IColumn ParseColumn(Parser yamlReader)
        {
            string columnName = "";
            string columnType = "";
            
            yamlReader.Consume<MappingStart>();
            
            while (yamlReader.Current != null && !yamlReader.Current.GetType().Equals(typeof(MappingEnd)))
            {
                if (yamlReader.Current is Scalar scalar)
                {
                    string key = scalar.Value;
                    yamlReader.Consume<Scalar>();
                    
                    if (key == "name" && yamlReader.Current is Scalar nameScalar)
                    {
                        columnName = nameScalar.Value;
                        yamlReader.Consume<Scalar>();
                    }
                    else if (key == "type" && yamlReader.Current is Scalar typeScalar)
                    {
                        columnType = typeScalar.Value;
                        yamlReader.Consume<Scalar>();
                    }
                    else
                    {
                        yamlReader.Consume();
                    }
                }
                else
                {
                    yamlReader.Consume();
                }
            }
            
            if (yamlReader.Current is MappingEnd)
            {
                yamlReader.Consume<MappingEnd>();
            }
            
            if (!string.IsNullOrEmpty(columnName) && !string.IsNullOrEmpty(columnType))
            {
                return YamlToDafnyTranslator.Column.create(
                    Dafny.Sequence<Dafny.Rune>.UnicodeFromString(columnName),
                    Dafny.Sequence<Dafny.Rune>.UnicodeFromString(columnType)
                );
            }
            
            return null;
        }
    }

    // Partial class extension to provide external function implementations
    public static partial class __default
    {
        // External function implementations
        public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ReadAllLines(Dafny.ISequence<Dafny.Rune> path)
        {
            return ExternalFunctions.ReadAllLines(path);
        }

        public static void WriteLine(Dafny.ISequence<Dafny.Rune> s)
        {
            ExternalFunctions.WriteLine(s);
        }

        public static Dafny.ISequence<YamlToDafnyTranslator._ITable> ParseYaml(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> lines)
        {
            return ExternalFunctions.ParseYaml(lines);
        }
    }
} 