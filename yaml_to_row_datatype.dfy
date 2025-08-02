module YamlToRowDatatypeTranslator {
  // Simple YAML reader that just reads lines from a file

  method {:extern "ExternalFunctions", "ReadAllLines"} ReadAllLines(path: string) returns (lines: seq<string>)

  // Data YAML parsing is delegated to externally supplied code
  method {:extern "ExternalFunctions", "ParseDataYaml"} ParseDataYaml(lines: seq<string>) returns (data: seq<Row>)

  method {:extern "ExternalFunctions", "WriteLine"} WriteLine(s: string)

  datatype Row = Row(tableName: string, values: seq<string>)

  // Generate a Dafny datatype declaration for a single table's rows
  function RowDatatypeAsString(tableName: string, valueCount: int): string {
    var header := "  datatype " + tableName + "Row = " + tableName + "Row(\n";
    var fields := "";
    var i := 0;
    while i < valueCount
      decreases valueCount - i
    {
      fields := fields + "    value" + i + ": string,\n";
      i := i + 1;
    }
    var footer := "  )\n";
    header + fields + footer
  }

  // Generate a complete module with row datatypes
  function ModuleAsString(data: seq<Row>, moduleName: string): string {
    var header := "module " + moduleName + " {\n\n";
    var footer := "}\n";
    var datatypes := "";
    
    // For now, generate datatypes for each unique table
    var i := 0;
    while i < data.Length
      decreases data.Length - i
    {
      var row := data[i];
      if row.values.Length > 0 {
        datatypes := datatypes + RowDatatypeAsString(row.tableName, row.values.Length);
      }
      i := i + 1;
    }
    
    header + datatypes + footer
  }
  
  // Main entry point - read the YAML file, parse it, and emit Dafny datatypes
  method Main(args: seq<string>)
  {
    if |args| < 2 {
      WriteLine("Usage: yaml_to_row_datatype <data.yml> [module_name]");
      return;
    }
    
    var path := args[1];
    var moduleName := if |args| >= 3 then args[2] else "GeneratedRowTypes";
    
    WriteLine("Reading file: " + path);
    var content := ReadAllLines(path);
    WriteLine("File read, parsing YAML...");
    var data := ParseDataYaml(content);
    WriteLine("YAML parsed, generating row datatypes...");
    
    WriteLine(ModuleAsString(data, moduleName));
    WriteLine("Done!");
  }
} 