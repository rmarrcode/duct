using System;
using System.IO;
using System.Collections.Generic;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;

public class YamlToDafnyTranslator {
  public static System.Collections.Generic.List<Table> ParseYaml(System.Collections.Generic.List<string> lines) {
    try {
      // Convert list of strings to YAML content
      string yamlContent = string.Join("\n", lines);
      
      var tables = new System.Collections.Generic.List<Table>();
      
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
      
      return tables;
    }
    catch (Exception ex) {
      Console.Error.WriteLine($"Error parsing YAML: {ex.Message}");
      return new System.Collections.Generic.List<Table>();
    }
  }

  private static Table ParseTable(Parser yamlReader) {
    string tableName = "";
    var columns = new System.Collections.Generic.List<Column>();
    
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
      return new Table(tableName, columns);
    }
    
    return null;
  }

  private static Column ParseColumn(Parser yamlReader) {
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
      return new Column(columnName, columnType);
    }
    
    return null;
  }

  public static System.Collections.Generic.List<string> ReadAllLines(string path) {
    try {
      return new System.Collections.Generic.List<string>(File.ReadAllLines(path));
    }
    catch (Exception ex) {
      Console.Error.WriteLine($"Error reading file: {ex.Message}");
      return new System.Collections.Generic.List<string>();
    }
  }

  public static void WriteLine(string s) {
    Console.WriteLine(s);
  }
} 