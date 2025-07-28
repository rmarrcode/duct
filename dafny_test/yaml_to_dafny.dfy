module YamlToDafnyTranslator {
  // ---------------------------------------------------------------------------
  // A **very small** YAML subset is supported:
  //
  // tables:
  //   - name: users
  //     columns:
  //       - name: id
  //         type: int
  //       - name: username
  //         type: string
  //   - name: posts
  //     columns:
  //       - name: id
  //         type: int
  //       - name: user_id
  //         type: int
  //       - name: content
  //         type: string
  //
  // In particular we only understand lists starting with "- " and simple
  // "key: value" pairs.  Indentation must be multiples of two spaces.
  // ---------------------------------------------------------------------------

  datatype Column = Column(name: string, typ: string)
  datatype Table  = Table(name: string, columns: seq<Column>)

  // ---------------------------------------------------------------------------
  // Helper – convert a list of columns into field declarations
  // ---------------------------------------------------------------------------
  function FieldLine(c: Column): string {
    "  var " + c.name + ": " + c.typ + ";\n"
  }

  function FieldsAsString(cols: seq<Column>): string {
    if |cols| == 0 then "" else FieldLine(cols[0]) + FieldsAsString(cols[1..])
  }

  // ---------------------------------------------------------------------------
  // Generate a Dafny class declaration for a single table.
  // ---------------------------------------------------------------------------
  function ClassAsString(t: Table): string {
    var header := "class " + t.name + " {\n";
    var footer := "}\n";
    header + FieldsAsString(t.columns) + footer
  }

  // ---------------------------------------------------------------------------
  // YAML parsing is delegated to externally supplied code (e.g. in C#).
  // ---------------------------------------------------------------------------
  // YAML parser – implemented in the back-end
  method {:extern} {:axiom} ParseYaml(lines: seq<string>) returns (tables: seq<Table>)
    ensures |tables| >= 0

  // ---------------------------------------------------------------------------
  // External helper methods for I/O.  These will be provided by the backend
  // (e.g. C#) when Dafny is compiled.
  // ---------------------------------------------------------------------------
  // File I/O helpers – also supplied by the back-end
  method {:extern} {:axiom} ReadAllLines(path: string) returns (lines: seq<string>)
    ensures |lines| >= 0

  method {:extern} {:axiom} WriteLine(s: string)

  // ---------------------------------------------------------------------------
  // Main entry point – for each file given on the command-line, read the YAML,
  // parse it, and emit Dafny classes.
  // ---------------------------------------------------------------------------
  method Main(args: seq<string>)
  {
    if |args| == 0 {
      WriteLine("Usage: yaml_to_dafny <file1.yml> [<file2.yml> ...]");
      return;
    }

    var idx := 0;
    while idx < |args|
      decreases |args| - idx
    {
      var path := args[idx];
      var content := ReadAllLines(path);
      var tables := ParseYaml(content);
      var j := 0;
      while j < |tables|
        decreases |tables| - j
      {
        WriteLine(ClassAsString(tables[j]));
        j := j + 1;
      }
      idx := idx + 1;
    }
  }
} 