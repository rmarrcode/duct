using System;
using System.Collections.Generic;

public class Column {
  public string name;
  public string typ;
  
  public Column(string name, string typ) {
    this.name = name;
    this.typ = typ;
  }
}

public class Table {
  public string name;
  public List<Column> columns;
  
  public Table(string name, List<Column> columns) {
    this.name = name;
    this.columns = columns;
  }
} 