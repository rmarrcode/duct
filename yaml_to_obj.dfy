module YamlToDafnyTranslator {
  // A very small YAML subset is supported:
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

  datatype Column = Column(name: string, typ: string)
  datatype Table  = Table(name: string, columns: seq<Column>)

  // Helper - convert a list of columns into field declarations
  function FieldLine(c: Column): string {
    "  var " + c.name + ": " + c.typ + ";\n"
  }

  function FieldsAsString(cols: seq<Column>): string {
    if |cols| == 0 then "" else FieldLine(cols[0]) + FieldsAsString(cols[1..])
  }

  // Generate a Dafny class declaration for a single table.
  function ClassAsString(t: Table): string {
    var header := "class " + t.name + " {\n";
    var footer := "}\n";
    header + FieldsAsString(t.columns) + footer
  }

  // YAML parsing is delegated to externally supplied code (e.g. in C++).
  // YAML parser - implemented in the back-end
  method {:extern "ExternalFunctions", "ParseYaml"} ParseYaml(lines: seq<string>) returns (tables: seq<Table>)

  method {:extern "ExternalFunctions", "ReadAllLines"} ReadAllLines(path: string) returns (lines: seq<string>)

  method {:extern "ExternalFunctions", "WriteLine"} WriteLine(s: string)

  // ------------------------------------------------------------
  // Simple in-memory "API" over a sequence of tables
  // ------------------------------------------------------------

  // Predicate: does a table with the given name exist?
  function TableExists(db: seq<Table>, name: string): bool {
    exists t :: t in db && t.name == name
  }

  // Create (add) a new table to the database.
  // Requires: no table of the same name already exists.
  // Ensures:  the returned database contains all previous tables plus the new one.
  function AddTable(db: seq<Table>, newT: Table): seq<Table>
    requires !TableExists(db, newT.name)
    ensures TableExists(result, newT.name)
    ensures |result| == |db| + 1
    ensures forall t :: t in db ==> t in result
  {
    db + [newT]
  }

  // Read (retrieve) all tables whose name matches the query.
  // If no such table exists the returned sequence is empty.
  function GetTables(db: seq<Table>, name: string): seq<Table>
    ensures (|result| == 0) ==> !TableExists(db, name)
    ensures forall t :: t in result ==> t.name == name
  {
    seq t | t in db && t.name == name :: t
  }

  // Update: replace an existing table (matched by name) with a modified one.
  // Requires: a table with the same name as `updated` must already exist.
  // Ensures:  length of database is unchanged and the returned database
  //           contains the updated table exactly once.
  function UpdateTable(db: seq<Table>, updated: Table): seq<Table>
    requires TableExists(db, updated.name)
    ensures |result| == |db|
    ensures TableExists(result, updated.name)
    ensures forall t :: t in result ==> t.name == updated.name ==> t == updated
  {
    seq t | t in db :: if t.name == updated.name then updated else t
  }

  // Delete: remove the table with the given name.
  // Requires: such a table exists.
  // Ensures:  the returned database no longer contains that table and is
  //           one element shorter than the input.
  function DeleteTable(db: seq<Table>, name: string): seq<Table>
    requires TableExists(db, name)
    ensures !TableExists(result, name)
    ensures |result| == |db| - 1
    ensures forall t :: t in result ==> t in db && t.name != name
  {
    seq t | t in db && t.name != name :: t
  }

  // Main entry point - for each file given on the command-line, read the YAML,
  // parse it, and emit Dafny classes.
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