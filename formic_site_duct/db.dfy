module DB {

  datatype DbTimestamp = DbTimestamp(value: string)

  datatype OptionalDbTimestamp =
    MissingTimestamp
  | PresentTimestamp(value: DbTimestamp)

  datatype PersistedUser = PersistedUser(
    email: string,
    name: string,
    picture: string
  )

  datatype UserCreds = FormicUser(
    id: int,
    user: PersistedUser,
    launch_token: LaunchToken
  )

  datatype LaunchToken = LaunchToken(
    id: int,
    user_id: int,
    token_hash: string,
    expires_at: DbTimestamp,
    used_at: OptionalDbTimestamp,
    created_at: DbTimestamp
  )

  datatype Session = Session(
    id: int,
    user_id: int,
    token_hash: string,
    expires_at: DbTimestamp,
    revoked_at: OptionalDbTimestamp,
    created_at: DbTimestamp,
    last_seen_at: DbTimestamp
  )

  datatype Table =
    PersistedUserTable
  | FormicUserTable
  | LaunchTokenTable
  | SessionTable

  datatype DbValue =
    DbPersistedUser(persistedUser: PersistedUser)
  | DbFormicUser(formicUser: UserCreds)
  | DbLaunchToken(launchToken: LaunchToken)
  | DbSession(session: Session)

  datatype DbKey =
    PersistedUserKey(email: string)
  | FormicUserKey(id: int)
  | LaunchTokenKey(id: int)
  | SessionKey(id: int)

  datatype DbChange =
    Put(row: DbValue)
  | Edit(key: DbKey, newValue: DbValue)
  | Delete(key: DbKey)

  datatype Patch =
    ReplaceWith(row: DbValue)

  datatype DbPred =
    TruePred
  | FalsePred
  | HasKeyPred(key: DbKey)
  | TableHasAnyPred(table: Table)
  | TableHasKeyPred(table: Table, key: DbKey)
  | NotPred(pred: DbPred)
  | AndPred(left: DbPred, right: DbPred)
  | OrPred(left: DbPred, right: DbPred)

  datatype DbQuery =
    AllRows
  | RowsInTable(table: Table)
  | RowWithKey(key: DbKey)
  | RowsMatching(pred: DbPred)

  datatype DbProgram =
    Return
  | Seq(p1: DbProgram, p2: DbProgram)
  | Lookup(table: Table, key: DbKey)
  | Exists(table: Table, pred: DbPred)
  | Insert(row: DbValue)
  | Update(key: DbKey, patch: Patch)
  | DeleteRow(key: DbKey)
  | If(cond: DbPred, thenP: DbProgram, elseP: DbProgram)
  | ForEach(query: DbQuery, body: DbProgram)

  function {:compile true} TableOf(row: DbValue): Table
  {
    match row
    case DbPersistedUser(_) => PersistedUserTable
    case DbFormicUser(_) => FormicUserTable
    case DbLaunchToken(_) => LaunchTokenTable
    case DbSession(_) => SessionTable
  }

  function {:compile true} KeyOf(row: DbValue): DbKey
  {
    match row
    case DbPersistedUser(persistedUser) => PersistedUserKey(persistedUser.email)
    case DbFormicUser(formicUser) => FormicUserKey(formicUser.id)
    case DbLaunchToken(launchToken) => LaunchTokenKey(launchToken.id)
    case DbSession(session) => SessionKey(session.id)
  }

  predicate ValidChange(change: DbChange)
  {
    match change
    case Put(_) => true
    case Edit(key, newValue) => key == KeyOf(newValue)
    case Delete(_) => true
  }

  function {:compile true} FilterEntries(entries: seq<DbValue>, key: DbKey): seq<DbValue>
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else if KeyOf(entries[0]) == key then
      FilterEntries(entries[1..], key)
    else
      [entries[0]] + FilterEntries(entries[1..], key)
  }

  function {:compile true} HasKey(entries: seq<DbValue>, key: DbKey): bool
    decreases |entries|
  {
    if |entries| == 0 then
      false
    else
      KeyOf(entries[0]) == key || HasKey(entries[1..], key)
  }

  function {:compile true} TableHasAny(entries: seq<DbValue>, table: Table): bool
    decreases |entries|
  {
    if |entries| == 0 then
      false
    else
      TableOf(entries[0]) == table || TableHasAny(entries[1..], table)
  }

  function {:compile true} TableHasKey(entries: seq<DbValue>, table: Table, key: DbKey): bool
    decreases |entries|
  {
    if |entries| == 0 then
      false
    else
      (TableOf(entries[0]) == table && KeyOf(entries[0]) == key)
      || TableHasKey(entries[1..], table, key)
  }

  function {:compile true} RowsForTable(entries: seq<DbValue>, table: Table): seq<DbValue>
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else if TableOf(entries[0]) == table then
      [entries[0]] + RowsForTable(entries[1..], table)
    else
      RowsForTable(entries[1..], table)
  }

  function {:compile true} RowsForKey(entries: seq<DbValue>, key: DbKey): seq<DbValue>
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else if KeyOf(entries[0]) == key then
      [entries[0]]
    else
      RowsForKey(entries[1..], key)
  }

  function {:compile true} EvalPred(entries: seq<DbValue>, pred: DbPred): bool
  {
    match pred
    case TruePred => true
    case FalsePred => false
    case HasKeyPred(key) => HasKey(entries, key)
    case TableHasAnyPred(table) => TableHasAny(entries, table)
    case TableHasKeyPred(table, key) => TableHasKey(entries, table, key)
    case NotPred(inner) => !EvalPred(entries, inner)
    case AndPred(left, right) => EvalPred(entries, left) && EvalPred(entries, right)
    case OrPred(left, right) => EvalPred(entries, left) || EvalPred(entries, right)
  }

  function {:compile true} EvalQuery(entries: seq<DbValue>, query: DbQuery): seq<DbValue>
  {
    match query
    case AllRows => entries
    case RowsInTable(table) => RowsForTable(entries, table)
    case RowWithKey(key) => RowsForKey(entries, key)
    case RowsMatching(pred) =>
      if EvalPred(entries, pred) then entries else []
  }

  function ProgramSize(program: DbProgram): nat
  {
    match program
    case Return => 1
    case Seq(p1, p2) => 1 + ProgramSize(p1) + ProgramSize(p2)
    case Lookup(_, _) => 1
    case Exists(_, _) => 1
    case Insert(_) => 1
    case Update(_, _) => 1
    case DeleteRow(_) => 1
    case If(_, thenP, elseP) => 1 + ProgramSize(thenP) + ProgramSize(elseP)
    case ForEach(_, body) => 1 + ProgramSize(body)
  }

  function {:compile true} PatchToChange(key: DbKey, patch: Patch): seq<DbChange>
  {
    match patch
    case ReplaceWith(row) =>
      if KeyOf(row) == key then [Edit(key, row)] else []
  }

  function {:compile true} ExecuteOperation(entries: seq<DbValue>, change: DbChange): seq<DbValue>
  {
    match change
    case Put(row) => FilterEntries(entries, KeyOf(row)) + [row]
    case Edit(key, newValue) =>
      if key == KeyOf(newValue) then
        FilterEntries(entries, key) + [newValue]
      else
        entries
    case Delete(key) => FilterEntries(entries, key)
  }

  function {:compile true} ExecuteOperations(entries: seq<DbValue>, changes: seq<DbChange>): seq<DbValue>
    decreases |changes|
  {
    if |changes| == 0 then
      entries
    else
      ExecuteOperations(ExecuteOperation(entries, changes[0]), changes[1..])
  }

  function {:compile true} ProgramOperationsForRows(entries: seq<DbValue>, rows: seq<DbValue>, body: DbProgram): seq<DbChange>
    decreases ProgramSize(body), |rows|
  {
    if |rows| == 0 then
      []
    else
      var ops := ProgramOperations(entries, body);
      ops + ProgramOperationsForRows(ExecuteOperations(entries, ops), rows[1..], body)
  }

  function {:compile true} ProgramOperations(entries: seq<DbValue>, program: DbProgram): seq<DbChange>
    decreases ProgramSize(program), 0
  {
    match program
    case Return => []
    case Seq(p1, p2) =>
      var ops1 := ProgramOperations(entries, p1);
      ops1 + ProgramOperations(ExecuteOperations(entries, ops1), p2)
    case Lookup(_, _) => []
    case Exists(_, _) => []
    case Insert(row) => [Put(row)]
    case Update(key, patch) => PatchToChange(key, patch)
    case DeleteRow(key) => [Delete(key)]
    case If(cond, thenP, elseP) =>
      if EvalPred(entries, cond) then
        ProgramOperations(entries, thenP)
      else
        ProgramOperations(entries, elseP)
    case ForEach(query, body) =>
      ProgramOperationsForRows(entries, EvalQuery(entries, query), body)
  }

  function {:compile true} ExecuteProgram(entries: seq<DbValue>, program: DbProgram): seq<DbValue>
  {
    ExecuteOperations(entries, ProgramOperations(entries, program))
  }

  /*
  Goal of DB is to guarantee that any specifications made on entries
  is reflected in actual DB. The concrete runtime state is an append-only
  log of DbChange values; Entries() is the as-if materialized view.
  */
  class Database {

    var operations: seq<DbChange>

    constructor ()
      ensures operations == []
    {
      operations := [];
    }

    ghost function Entries(): seq<DbValue>
      reads this
    {
      ExecuteOperations([], operations)
    }

    method ApplyOperations(changes: seq<DbChange>)
      modifies this
      ensures operations == old(operations) + changes
    {
      operations := operations + changes;
    }

    method GetOperations() returns (ops: seq<DbChange>)
      ensures ops == operations
    {
      ops := operations;
    }
  }
}
