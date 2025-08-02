module YamlToDatatypeTranslator {
  // Simple YAML reader that just reads lines from a file

  method {:extern "ExternalFunctions", "ReadAllLines"} ReadAllLines(path: string) returns (lines: seq<string>)

  // YAML parsing is delegated to externally supplied code
  method {:extern "ExternalFunctions", "ParseYaml"} ParseYaml(lines: seq<string>) returns (tables: seq<Table>)

  method {:extern "ExternalFunctions", "WriteLine"} WriteLine(s: string)

  datatype Column = Column(name: string, typ: string)
  datatype Table  = Table(name: string, columns: seq<Column>)

  // Helper - convert a list of columns into field declarations for datatypes
  function DatatypeFieldLine(c: Column): string {
    "    " + c.name + ": " + c.typ + ",\n"
  }

  function DatatypeFieldsAsString(cols: seq<Column>): string {
    if cols.Length == 0 then "" else DatatypeFieldLine(cols[0]) + DatatypeFieldsAsString(cols[1..])
  }

  // Generate a Dafny datatype declaration for a single table.
  function DatatypeAsString(t: Table): string {
    var header := "  datatype " + t.name + " = " + t.name + "(\n";
    var footer := "  )\n";
    header + DatatypeFieldsAsString(t.columns) + footer
  }

  // Generate a complete module with datatypes
  function ModuleAsString(tables: seq<Table>, moduleName: string): string {
    var header := "module " + moduleName + " {\n\n";
    var footer := "}\n";
    var datatypes := "";
    var i := 0;
    while i < |tables|
      decreases |tables| - i
    {
      datatypes := datatypes + DatatypeAsString(tables[i]);
      i := i + 1;
    }
    header + datatypes + footer
  }
  
  // Main entry point - read the YAML file, parse it, and emit Dafny datatypes
  method Main(args: seq<string>)
  {
    if |args| < 2 {
      WriteLine("Usage: yaml_to_datatype <file.yml> [module_name]");
      return;
    }
    
    var path := args[1];
    var moduleName := if |args| >= 3 then args[2] else "GeneratedTypes";
    
    WriteLine("Reading file: " + path);
    var content := ReadAllLines(path);
    WriteLine("File read, parsing YAML...");
    var tables := ParseYaml(content);
    WriteLine("YAML parsed, generating datatypes...");
    
    WriteLine(ModuleAsString(tables, moduleName));
    WriteLine("Done!");
  }
} 