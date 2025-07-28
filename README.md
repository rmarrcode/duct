# YAML to Dafny Translator

This project implements a YAML to Dafny class translator. It reads YAML files containing table definitions and generates corresponding Dafny class declarations.

## Project Structure

- `yaml_to_obj.cs` - The original Dafny-compiled C# program (kept for reference, not modified)
- `Program.cs` - New main entry point that links external functions with the original program
- `ExternalFunctions.cs` - Implementation of external functions for YAML parsing and I/O
- `YamlToDafnyTranslator.csproj` - C# project file with dependencies
- `test_tables.yml` - Sample YAML file for testing

## Dependencies

The project requires:
- .NET 6.0 or later
- YamlDotNet library for YAML parsing
- System.Runtime.Numerics and System.Collections.Immutable (included in project)

## Building the Project

```bash
cd duct
dotnet restore
dotnet build
```

## Running the Translator

```bash
# Build the project
dotnet build

# Run with a YAML file
dotnet run test_tables.yml

# Run with multiple YAML files
dotnet run file1.yml file2.yml file3.yml
```

## YAML Format

The translator expects YAML files with the following structure:

```yaml
tables:
  - name: table_name
    columns:
      - name: column_name
        type: column_type
      - name: another_column
        type: another_type
```

## Output

The program generates Dafny class declarations for each table defined in the YAML file. For example:

```dafny
class users {
  var id: int;
  var username: string;
  var email: string;
}

class posts {
  var id: int;
  var user_id: int;
  var title: string;
  var content: string;
  var created_at: datetime;
}
```

## External Functions

The following external functions are implemented in `ExternalFunctions.cs`:

1. `ReadAllLines(path: string) returns (lines: seq<string>)` - Reads all lines from a file
2. `WriteLine(s: string)` - Writes a string to console output
3. `ParseYaml(lines: seq<string>) returns (tables: seq<Table>)` - Parses YAML content and returns table definitions

These functions are linked to the main program through the `Program.cs` file, which provides a new entry point that implements the external functions without modifying the original `yaml_to_obj.cs` file. 