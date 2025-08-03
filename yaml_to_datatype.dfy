module YamlToSchemaDatatypeTranslator {
  // Simple YAML reader that just reads lines from a file

  method {:extern "ExternalFunctions", "ReadAllLines"} ReadAllLines(path: string) returns (lines: seq<string>)

  method {:extern "ExternalFunctions", "ParseSchemaYaml"} ParseSchemaYaml(lines: seq<string>) returns (tables: seq<Table>)

  method {:extern "ExternalFunctions", "WriteLine"} WriteLine(s: string)

  method {:extern "ExternalFunctions", "WriteToFile"} WriteToFile(filename: string, content: string)

  datatype Column = Column(name: string, typ: string)
  datatype Table  = Table(name: string, columns: seq<Column>)

  // Generate a Dafny datatype declaration for a single table schema
  function SchemaDatatypeAsString(t: Table): string {
    var header := "  datatype " + t.name + " = " + t.name + "(\n";
    var fields := SchemaFieldsAsString(t.columns);
    var footer := "  )\n";
    header + fields + footer
  }

  // Helper function to generate fields string
  function SchemaFieldsAsString(cols: seq<Column>): string {
    if |cols| == 0 then "" else "    " + cols[0].name + ": " + cols[0].typ + ",\n" + SchemaFieldsAsString(cols[1..])
  }

  // Generate a complete module with schema datatypes
  function ModuleAsString(tables: seq<Table>, moduleName: string): string {
    var header := "module " + moduleName + " {\n\n";
    var footer := "}\n";
    var datatypes := ModuleDatatypesAsString(tables);
    header + datatypes + footer
  }

  // Helper function to generate datatypes string
  function ModuleDatatypesAsString(tables: seq<Table>): string {
    if |tables| == 0 then "" else SchemaDatatypeAsString(tables[0]) + ModuleDatatypesAsString(tables[1..])
  }
  
  // Main entry point - read the YAML file, parse it, and emit Dafny datatypes
  method Main(args: seq<string>)
  {
    if |args| < 2 {
      WriteLine("Usage: yaml_to_schema_datatype <schema.yml> [output_file] [module_name]");
      return;
    }
    
    var path := args[1];
    var outputFile := if |args| >= 3 then args[2] else "generated_schema_types.dfy";
    var moduleName := if |args| >= 4 then args[3] else "GeneratedSchemaTypes";
    
    WriteLine("Reading file: " + path);
    var content := ReadAllLines(path);
    WriteLine("File read, parsing YAML...");
    var tables := ParseSchemaYaml(content);
    WriteLine("YAML parsed, generating schema datatypes...");
    
    var generatedCode := ModuleAsString(tables, moduleName);
    WriteLine("Generated code:");
    WriteLine(generatedCode);
    WriteToFile(outputFile, generatedCode);
    WriteLine("Code written to: " + outputFile);
    WriteLine("Done!");
  }
} 