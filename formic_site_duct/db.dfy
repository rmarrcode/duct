module DB {

  import opened DuctTools

  // import opened DuctTools

  // Store timestamps as ISO-8601 strings at the boundary to keep the schema
  // simple for generated C# and later host-side persistence adapters.
  datatype DbTimestamp = DbTimestamp(value: string)

  datatype OptionalDbTimestamp =
    MissingTimestamp
  | PresentTimestamp(value: DbTimestamp)

  datatype PersistedUser = PersistedUser(
    email: string,
    name: string,
    picture: string
  )

  // users table
  datatype UserCreds = FormicUser(
    id: int,
    user: UserInfo,
    launch_token: LaunchToken
  )

  // launch_tokens table
  datatype LaunchToken = LaunchToken(
    id: int,
    user_id: int,
    token_hash: string,
    expires_at: DbTimestamp,
    used_at: OptionalDbTimestamp,
    created_at: DbTimestamp
  )

  // sessions table
  datatype Session = Session(
    id: int,
    user_id: int,
    token_hash: string,
    expires_at: DbTimestamp,
    revoked_at: OptionalDbTimestamp,
    created_at: DbTimestamp,
    last_seen_at: DbTimestamp
  )
}
