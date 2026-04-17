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

  /*
  Goal of DB is to guarantee that any specifications made on entries 
  is reflected in actual DB
  */
  class Database {

    var entries: seq<DbValue>

    constructor ()
      ensures entries == []
    {
      entries := [];
    }
  }

  //method {:extern "DuctDbBridge", "Persist"} {:axiom} Persist(db: Database, value: DbValue)
    //ensures db.entries == old(db.entries)
}
