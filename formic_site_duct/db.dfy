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

  function {:compile true} ExecuteOperation(entries: seq<DbValue>, change: DbChange): seq<DbValue>
    requires ValidChange(change)
  {
    match change
    case Put(row) => FilterEntries(entries, KeyOf(row)) + [row]
    case Edit(key, newValue) => FilterEntries(entries, key) + [newValue]
    case Delete(key) => FilterEntries(entries, key)
  }

  function {:compile true} ExecuteOperations(entries: seq<DbValue>, changes: seq<DbChange>): seq<DbValue>
    requires forall i :: 0 <= i < |changes| ==> ValidChange(changes[i])
    decreases |changes|
  {
    if |changes| == 0 then
      entries
    else
      ExecuteOperations(ExecuteOperation(entries, changes[0]), changes[1..])
  }

  /*
  Goal of DB is to guarantee that any specifications made on entries
  is reflected in actual DB.
  */
  class Database {

    var entries: seq<DbValue>
    var operations: seq<DbChange>

    constructor ()
      ensures entries == []
      ensures operations == []
    {
      entries := [];
      operations := [];
    }

    method ApplyOperation(change: DbChange)
      requires ValidChange(change)
      modifies this
      ensures entries == ExecuteOperation(old(entries), change)
      ensures operations == old(operations) + [change]
    {
      entries := ExecuteOperation(entries, change);
      operations := operations + [change];
    }

    method ApplyOperations(changes: seq<DbChange>)
      requires forall i :: 0 <= i < |changes| ==> ValidChange(changes[i])
      modifies this
      ensures entries == ExecuteOperations(old(entries), changes)
      ensures operations == old(operations) + changes
    {
      entries := ExecuteOperations(entries, changes);
      operations := operations + changes;
    }
  }
}
