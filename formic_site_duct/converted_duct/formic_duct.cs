// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.9.0.0
// Command-line arguments: translate cs /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/db.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/duct.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/formic.specs.duct.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/implementations/landing_page.program.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/implementations/login_challenge.program.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/implementations/save_user.program.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/implementations/secure_page.program.dfy /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/formic.apis.duct.dfy --no-verify --allow-warnings --include-runtime --output /home/ryan-marr/Documents/secret/duct_env/duct/formic_site_duct/converted_duct/formic_duct
// the_program


module DB {
  function {:compile true} TableOf(row: DbValue): Table
    decreases row
  {
    match row
    case DbPersistedUser(_ /* _v0 */) =>
      PersistedUserTable
    case DbFormicUser(_ /* _v1 */) =>
      FormicUserTable
    case DbLaunchToken(_ /* _v2 */) =>
      LaunchTokenTable
    case DbSession(_ /* _v3 */) =>
      SessionTable
  }

  function {:compile true} KeyOf(row: DbValue): DbKey
    decreases row
  {
    match row
    case DbPersistedUser(persistedUser) =>
      PersistedUserKey(persistedUser.email)
    case DbFormicUser(formicUser) =>
      FormicUserKey(formicUser.id)
    case DbLaunchToken(launchToken) =>
      LaunchTokenKey(launchToken.id)
    case DbSession(session) =>
      SessionKey(session.id)
  }

  predicate ValidChange(change: DbChange)
    decreases change
  {
    match change
    case Put(_ /* _v4 */) =>
      true
    case Edit(key, newValue) =>
      key == KeyOf(newValue)
    case Delete(_ /* _v5 */) =>
      true
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
      (TableOf(entries[0]) == table && KeyOf(entries[0]) == key) || TableHasKey(entries[1..], table, key)
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
    decreases entries, pred
  {
    match pred
    case TruePred() =>
      true
    case FalsePred() =>
      false
    case HasKeyPred(key) =>
      HasKey(entries, key)
    case TableHasAnyPred(table) =>
      TableHasAny(entries, table)
    case TableHasKeyPred(table, key) =>
      TableHasKey(entries, table, key)
    case NotPred(inner) =>
      !EvalPred(entries, inner)
    case AndPred(left, right) =>
      EvalPred(entries, left) &&
      EvalPred(entries, right)
    case OrPred(left, right) =>
      EvalPred(entries, left) || EvalPred(entries, right)
  }

  function {:compile true} EvalQuery(entries: seq<DbValue>, query: DbQuery): seq<DbValue>
    decreases entries, query
  {
    match query
    case AllRows() =>
      entries
    case RowsInTable(table) =>
      RowsForTable(entries, table)
    case RowWithKey(key) =>
      RowsForKey(entries, key)
    case RowsMatching(pred) =>
      if EvalPred(entries, pred) then
        entries
      else
        []
  }

  function ProgramSize(program: DbProgram): nat
    decreases program
  {
    match program
    case Return() =>
      1
    case Seq(p1, p2) =>
      1 + ProgramSize(p1) + ProgramSize(p2)
    case Lookup(_ /* _v6 */, _ /* _v7 */) =>
      1
    case Exists(_ /* _v8 */, _ /* _v9 */) =>
      1
    case Insert(_ /* _v10 */) =>
      1
    case Update(_ /* _v11 */, _ /* _v12 */) =>
      1
    case DeleteRow(_ /* _v13 */) =>
      1
    case If(_ /* _v14 */, thenP, elseP) =>
      1 + ProgramSize(thenP) + ProgramSize(elseP)
    case ForEach(_ /* _v15 */, body) =>
      1 + ProgramSize(body)
  }

  function {:compile true} PatchToChange(key: DbKey, patch: Patch): seq<DbChange>
    decreases key, patch
  {
    match patch
    case ReplaceWith(row) =>
      if KeyOf(row) == key then
        [Edit(key, row)]
      else
        []
  }

  function {:compile true} ExecuteOperation(entries: seq<DbValue>, change: DbChange): seq<DbValue>
    decreases entries, change
  {
    match change
    case Put(row) =>
      FilterEntries(entries, KeyOf(row)) + [row]
    case Edit(key, newValue) =>
      if key == KeyOf(newValue) then
        FilterEntries(entries, key) + [newValue]
      else
        entries
    case Delete(key) =>
      FilterEntries(entries, key)
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
      var ops: seq<DbChange> := ProgramOperations(entries, body); ops + ProgramOperationsForRows(ExecuteOperations(entries, ops), rows[1..], body)
  }

  function {:compile true} ProgramOperations(entries: seq<DbValue>, program: DbProgram): seq<DbChange>
    decreases ProgramSize(program), 0
  {
    match program
    case Return() =>
      []
    case Seq(p1, p2) =>
      var ops1: seq<DbChange> := ProgramOperations(entries, p1);
      ops1 + ProgramOperations(ExecuteOperations(entries, ops1), p2)
    case Lookup(_ /* _v16 */, _ /* _v17 */) =>
      []
    case Exists(_ /* _v18 */, _ /* _v19 */) =>
      []
    case Insert(row) =>
      [Put(row)]
    case Update(key, patch) =>
      PatchToChange(key, patch)
    case DeleteRow(key) =>
      [Delete(key)]
    case If(cond, thenP, elseP) =>
      if EvalPred(entries, cond) then
        ProgramOperations(entries, thenP)
      else
        ProgramOperations(entries, elseP)
    case ForEach(query, body) =>
      ProgramOperationsForRows(entries, EvalQuery(entries, query), body)
  }

  function {:compile true} ExecuteProgram(entries: seq<DbValue>, program: DbProgram): seq<DbValue>
    decreases entries, program
  {
    ExecuteOperations(entries, ProgramOperations(entries, program))
  }

  datatype DbTimestamp = DbTimestamp(value: string)

  datatype OptionalDbTimestamp = MissingTimestamp | PresentTimestamp(value: DbTimestamp)

  datatype PersistedUser = PersistedUser(email: string, name: string, picture: string)

  datatype UserCreds = FormicUser(id: int, user: PersistedUser, launch_token: LaunchToken)

  datatype LaunchToken = LaunchToken(id: int, user_id: int, token_hash: string, expires_at: DbTimestamp, used_at: OptionalDbTimestamp, created_at: DbTimestamp)

  datatype Session = Session(id: int, user_id: int, token_hash: string, expires_at: DbTimestamp, revoked_at: OptionalDbTimestamp, created_at: DbTimestamp, last_seen_at: DbTimestamp)

  datatype Table = PersistedUserTable | FormicUserTable | LaunchTokenTable | SessionTable

  datatype DbValue = DbPersistedUser(persistedUser: PersistedUser) | DbFormicUser(formicUser: UserCreds) | DbLaunchToken(launchToken: LaunchToken) | DbSession(session: Session)

  datatype DbKey = PersistedUserKey(email: string) | FormicUserKey(id: int) | LaunchTokenKey(id: int) | SessionKey(id: int)

  datatype DbChange = Put(row: DbValue) | Edit(key: DbKey, newValue: DbValue) | Delete(key: DbKey)

  datatype Patch = ReplaceWith(row: DbValue)

  datatype DbPred = TruePred | FalsePred | HasKeyPred(key: DbKey) | TableHasAnyPred(table: Table) | TableHasKeyPred(table: Table, key: DbKey) | NotPred(pred: DbPred) | AndPred(left: DbPred, right: DbPred) | OrPred(left: DbPred, right: DbPred)

  datatype DbQuery = AllRows | RowsInTable(table: Table) | RowWithKey(key: DbKey) | RowsMatching(pred: DbPred)

  datatype DbProgram = Return | Seq(p1: DbProgram, p2: DbProgram) | Lookup(table: Table, key: DbKey) | Exists(table: Table, pred: DbPred) | Insert(row: DbValue) | Update(key: DbKey, patch: Patch) | DeleteRow(key: DbKey) | If(cond: DbPred, thenP: DbProgram, elseP: DbProgram) | ForEach(query: DbQuery, body: DbProgram)

  class Database {
    var operations: seq<DbChange>

    constructor ()
      ensures operations == []
    {
      operations := [];
    }

    ghost function Entries(): seq<DbValue>
      reads this
      decreases {this}
    {
      ExecuteOperations([], operations)
    }

    method ApplyOperations(changes: seq<DbChange>)
      modifies this
      ensures operations == old(operations) + changes
      decreases changes
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

module DuctTools {

  import opened DB
  datatype UserInfo = UserInfo(name: string, email: string, picture: string, authenticated: bool)

  datatype ReturnType = Content(body: string) | ChallengeGoogle(returnUrl: string) | Redirect(url: string)

  trait IGeneratorSpec {
    predicate PreCondition(u: UserInfo)
      decreases u

    ghost predicate PostCondition(u: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
      decreases u, before, payload, after
  }

  trait {:termination false} IGeneratorCore extends IGeneratorSpec {
    function Program(u: UserInfo): DbProgram
      decreases u

    function Response(u: UserInfo): ReturnType
      decreases u

    ghost predicate ImplementationCorrect(u: UserInfo)
      decreases u
    {
      forall before: seq<DbValue> {:trigger ExecuteProgram(before, Program(u))} :: 
        PostCondition(u, before, Response(u), ExecuteProgram(before, Program(u)))
    }

    ghost predicate GeneratePost(u: UserInfo, payload: ReturnType, prog: DbProgram)
      decreases u, payload, prog
    {
      payload == Response(u) &&
      prog == Program(u) &&
      forall before: seq<DbValue> {:trigger ExecuteProgram(before, prog)} :: 
        PostCondition(u, before, payload, ExecuteProgram(before, prog))
    }

    method Generate(u: UserInfo) returns (payload: ReturnType, prog: DbProgram)
      requires PreCondition(u)
      ensures payload == Response(u)
      ensures prog == Program(u)
      decreases u
    {
      payload := Response(u);
      prog := Program(u);
    }
  }

  class ApiEndpoint {
    var apiUrl: string
    var returnType: ReturnType
    var generator: IGeneratorCore

    constructor (apiUrl: string, rt: ReturnType, generator: IGeneratorCore)
      requires apiUrl != """"
      requires apiUrl[0] == '/'
      ensures this.apiUrl == apiUrl
      ensures this.returnType == rt
      ensures this.generator == generator
      decreases apiUrl, rt, generator
    {
      this.apiUrl := apiUrl;
      this.returnType := rt;
      this.generator := generator;
    }
  }

  class AllApiEndpoints {
    var endpoints: seq<ApiEndpoint>

    constructor ()
      ensures endpoints == []
    {
      endpoints := [];
    }

    method Add(ep: ApiEndpoint)
      modifies this
      ensures endpoints == old(endpoints) + [ep]
      decreases ep
    {
      endpoints := endpoints + [ep];
    }

    method Count() returns (n: int)
      ensures n == |endpoints|
    {
      n := |endpoints|;
    }

    method Get(i: int) returns (ep: ApiEndpoint)
      requires 0 <= i < |endpoints|
      ensures ep == endpoints[i]
      decreases i
    {
      ep := endpoints[i];
    }
  }
}

module SpecsTools {
  function Contains(haystack: string, needle: string): bool
    decreases |haystack|
  {
    if |needle| == 0 then
      true
    else if |haystack| < |needle| then
      false
    else
      haystack[0 .. |needle|] == needle || Contains(haystack[1..], needle)
  }

  function {:compile true} Link(linkLabel: string, url: string): string
    decreases linkLabel, url
  {
    ""<a href=\"""" + url + ""\"">"" + linkLabel + ""</a>""
  }
}

module DuctSpecs {
  predicate LandingPagePre(ctx: UserInfo)
    decreases ctx
  {
    ctx.name != """" &&
    !Contains(ctx.name, ""Signed in"") &&
    !Contains(ctx.name, ""Anonymous"") &&
    !Contains(ctx.name, Link(""Log out"", ""/logout"")) &&
    !Contains(ctx.name, Link(""Sign in"", ""/login"")) &&
    !Contains(ctx.email, ""Signed in"") &&
    !Contains(ctx.email, ""Anonymous"") &&
    !Contains(ctx.email, Link(""Log out"", ""/logout"")) &&
    !Contains(ctx.email, Link(""Sign in"", ""/login"")) &&
    !Contains(ctx.picture, ""Signed in"") &&
    !Contains(ctx.picture, ""Anonymous"") &&
    !Contains(ctx.picture, Link(""Log out"", ""/logout"")) &&
    !Contains(ctx.picture, Link(""Sign in"", ""/login""))
  }

  predicate LandingPagePayloadPost(ctx: UserInfo, payload: ReturnType)
    decreases ctx, payload
  {
    payload.Content? &&
    var html: string := payload.body; html != """" && Contains(html, ctx.name) && (ctx.email == """" || Contains(html, ctx.email)) && (ctx.picture == """" || Contains(html, ctx.picture)) && ctx.authenticated == (Contains(html, ""Signed in"") && Contains(html, Link(""Log out"", ""/logout""))) && !ctx.authenticated == (Contains(html, ""Anonymous"") && Contains(html, Link(""Sign in"", ""/login"")))
  }

  predicate LandingPagePost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
    decreases ctx, before, payload, after
  {
    LandingPagePayloadPost(ctx, payload) &&
    after == before
  }

  predicate LoginPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
    decreases ctx, before, payload, after
  {
    payload == ReturnType.ChallengeGoogle(""/save_user"") &&
    after == before
  }

  predicate SecurePost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
    decreases ctx, before, payload, after
  {
    after == before &&
    if ctx.authenticated then payload.Content? && Contains(payload.body, ctx.name) && Contains(payload.body, ""You are authenticated"") else payload == ReturnType.ChallengeGoogle(""/secure"")
  }

  function {:compile true} SaveUserOperations(ctx: UserInfo): seq<DbChange>
    decreases ctx
  {
    if ctx.authenticated && ctx.email != """" then
      [DbChange.Put(DbValue.DbPersistedUser(PersistedUser(ctx.email, ctx.name, ctx.picture)))]
    else
      []
  }

  predicate SaveUserPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
    decreases ctx, before, payload, after
  {
    if ctx.authenticated && ctx.email != """" then
      var row: DbValue := DbPersistedUser(PersistedUser(ctx.email, ctx.name, ctx.picture));
      payload == Redirect(""/"") &&
      after == FilterEntries(before, PersistedUserKey(ctx.email)) + [row]
    else
      payload == ChallengeGoogle(""/save_user"") && after == before
  }

  import opened DuctTools

  import opened SpecsTools

  import opened DB

  trait {:termination false} LandingPageSpec extends IGeneratorCore {
    predicate PreCondition(u: UserInfo)
      decreases u
    {
      LandingPagePre(u)
    }

    ghost predicate PostCondition(u: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
      decreases u, before, payload, after
    {
      LandingPagePost(u, before, payload, after)
    }
  }

  trait {:termination false} LoginChallengePageSpec extends IGeneratorCore {
    predicate PreCondition(u: UserInfo)
      decreases u
    {
      true
    }

    ghost predicate PostCondition(u: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
      decreases u, before, payload, after
    {
      LoginPost(u, before, payload, after)
    }
  }

  trait {:termination false} SaveUserPageSpec extends IGeneratorCore {
    predicate PreCondition(u: UserInfo)
      decreases u
    {
      true
    }

    ghost predicate PostCondition(u: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
      decreases u, before, payload, after
    {
      SaveUserPost(u, before, payload, after)
    }
  }

  trait {:termination false} SecurePageSpec extends IGeneratorCore {
    predicate PreCondition(u: UserInfo)
      decreases u
    {
      true
    }

    ghost predicate PostCondition(u: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
      decreases u, before, payload, after
    {
      SecurePost(u, before, payload, after)
    }
  }
}

module DuctLandingImpl {
  function LandingPageStatus(ctx: UserInfo): string
    decreases ctx
  {
    if ctx.authenticated then
      ""Signed in""
    else
      ""Anonymous""
  }

  function LandingPageAction(ctx: UserInfo): string
    decreases ctx
  {
    if ctx.authenticated then
      Link(""Log out"", ""/logout"")
    else
      Link(""Sign in"", ""/login"")
  }

  function LandingPagePicturePanel(ctx: UserInfo): string
    decreases ctx
  {
    if ctx.picture == """" then
      ""<div class=\""avatar avatar-fallback\"">F</div>""
    else
      ""<div class=\""avatar\""><img src=\"""" + ctx.picture + ""\"" alt=\"""" + ctx.name + ""\"" /></div>""
  }

  function LandingPageEmailPanel(ctx: UserInfo): string
    decreases ctx
  {
    if ctx.email == """" then
      ""<span class=\""meta-value muted\"">No email linked</span>""
    else
      ""<span class=\""meta-value\"">"" + ctx.email + ""</span>""
  }

  function LandingPagePictureMeta(ctx: UserInfo): string
    decreases ctx
  {
    if ctx.picture == """" then
      ""<span class=\""meta-value muted\"">No profile photo</span>""
    else
      ""<span class=\""meta-value\"">Profile image connected</span>""
  }

  function LandingPageHtml(ctx: UserInfo): string
    decreases ctx
  {
    var status: string := LandingPageStatus(ctx);
    var action: string := LandingPageAction(ctx);
    ""<!doctype html><html lang=\""en\""><head><meta charset=\""utf-8\"" />"" + ""<meta name=\""viewport\"" content=\""width=device-width, initial-scale=1\"" />"" + ""<title>Formic</title>"" + ""<style>"" + "":root{--bg:#f7f3ea;--ink:#171717;--muted:#63635f;--card:#fffdf8;--accent:#0f766e;--line:rgba(23,23,23,.12);}"" + ""*{box-sizing:border-box;}body{margin:0;font-family:\""Avenir Next\"",\""Segoe UI\"",sans-serif;background:linear-gradient(180deg,#faf7f0,#ebe7dd);color:var(--ink);}"" + "".shell{min-height:100vh;display:grid;place-items:center;padding:32px 18px;}"" + "".panel{width:min(920px,100%);background:rgba(255,253,248,.92);border:1px solid var(--line);border-radius:20px;overflow:hidden;box-shadow:0 24px 70px rgba(23,23,23,.12);}"" + "".hero{display:grid;grid-template-columns:150px 1fr;gap:26px;padding:32px;border-bottom:1px solid var(--line);}"" + "".avatar{width:150px;height:150px;border-radius:18px;overflow:hidden;background:#e5e0d6;border:1px solid var(--line);display:grid;place-items:center;}"" + "".avatar img{width:100%;height:100%;object-fit:cover;display:block;}"" + "".avatar-fallback{font-size:52px;font-weight:800;color:var(--accent);letter-spacing:.08em;}"" + "".eyebrow{margin:0 0 10px;font-size:12px;letter-spacing:.18em;text-transform:uppercase;color:var(--accent);}"" + "".title{margin:0;font-size:42px;line-height:1;font-weight:800;}"" + "".status-badge{display:inline-flex;align-items:center;gap:10px;margin-top:16px;padding:9px 14px;border-radius:999px;background:#fff;border:1px solid var(--line);font-size:14px;font-weight:700;}"" + "".status-dot{width:10px;height:10px;border-radius:999px;background:var(--accent);}"" + "".lede{margin:18px 0 0;color:var(--muted);font-size:16px;line-height:1.6;max-width:42rem;}"" + "".content{display:grid;grid-template-columns:1.2fr .9fr;gap:20px;padding:28px 32px 32px;}"" + "".card{padding:22px;border-radius:14px;background:rgba(255,255,255,.7);border:1px solid var(--line);}"" + "".card-title{margin:0 0 16px;font-size:13px;letter-spacing:.16em;text-transform:uppercase;color:var(--muted);}"" + "".meta-grid{display:grid;gap:14px;}"" + "".meta-row{display:flex;justify-content:space-between;gap:18px;padding-bottom:12px;border-bottom:1px solid rgba(23,23,23,.08);}"" + "".meta-row:last-child{border-bottom:0;padding-bottom:0;}"" + "".meta-label{font-weight:700;color:var(--muted);}"" + "".meta-value{text-align:right;font-weight:600;max-width:22rem;overflow-wrap:anywhere;}"" + "".muted{color:var(--muted);font-weight:500;}"" + "".actions{display:flex;flex-wrap:wrap;gap:12px;margin-top:22px;}"" + "".actions a{display:inline-flex;align-items:center;justify-content:center;padding:13px 18px;border-radius:999px;text-decoration:none;font-weight:800;background:var(--accent);color:#fff;}"" + "".aside-copy{margin:0;color:var(--muted);line-height:1.7;}"" + ""@media (max-width:780px){.hero,.content{grid-template-columns:1fr;}.avatar{width:112px;height:112px;border-radius:14px;}.title{font-size:34px;}}"" + ""</style></head><body>"" + ""<main class=\""shell\""><section class=\""panel\"">"" + ""<div class=\""hero\"">"" + LandingPagePicturePanel(ctx) + ""<div>"" + ""<p class=\""eyebrow\"">Formic Landing Page</p>"" + ""<h1 class=\""title\"">"" + ctx.name + ""</h1>"" + ""<div class=\""status-badge\""><span class=\""status-dot\""></span>"" + status + ""</div>"" + ""<p class=\""lede\"">A generated profile surface for the formic demo.</p>"" + ""</div></div>"" + ""<div class=\""content\"">"" + ""<section class=\""card\"">"" + ""<p class=\""card-title\"">Profile</p>"" + ""<div class=\""meta-grid\"">"" + ""<div class=\""meta-row\""><span class=\""meta-label\"">Name</span><span class=\""meta-value\"">"" + ctx.name + ""</span></div>"" + ""<div class=\""meta-row\""><span class=\""meta-label\"">Email</span>"" + LandingPageEmailPanel(ctx) + ""</div>"" + ""<div class=\""meta-row\""><span class=\""meta-label\"">Picture</span>"" + LandingPagePictureMeta(ctx) + ""</div>"" + ""<div class=\""meta-row\""><span class=\""meta-label\"">Session</span><span class=\""meta-value\"">"" + status + ""</span></div>"" + ""</div>"" + ""<div class=\""actions\"">"" + action + ""</div>"" + ""</section>"" + ""<aside class=\""card\"">"" + ""<p class=\""card-title\"">Notes</p>"" + ""<p class=\""aside-copy\"">This page is generated from Dafny and rendered through the ASP.NET host.</p>"" + ""</aside>"" + ""</div></section></main></body></html>""
  }

  import opened DB

  import opened DuctTools

  import opened DuctSpecs

  import opened SpecsTools

  class FormicLandingPage extends LandingPageSpec {
    constructor ()
    {
    }

    function Response(u: UserInfo): ReturnType
      decreases u
    {
      Content(LandingPageHtml(u))
    }

    function Program(u: UserInfo): DbProgram
      decreases u
    {
      Return
    }
  }
}

module DuctLoginImpl {

  import opened DB

  import opened DuctTools

  import opened DuctSpecs
  class LoginChallengePage extends LoginChallengePageSpec {
    constructor ()
    {
    }

    function Response(u: UserInfo): ReturnType
      decreases u
    {
      ChallengeGoogle(""/save_user"")
    }

    function Program(u: UserInfo): DbProgram
      decreases u
    {
      Return
    }
  }
}

module DuctSaveUserImpl {

  import opened DB

  import opened DuctTools

  import opened DuctSpecs
  class SaveUserPage extends SaveUserPageSpec {
    constructor ()
    {
    }

    function Response(u: UserInfo): ReturnType
      decreases u
    {
      if u.authenticated && u.email != """" then
        Redirect(""/"")
      else
        ChallengeGoogle(""/save_user"")
    }

    function Program(u: UserInfo): DbProgram
      decreases u
    {
      if u.authenticated && u.email != """" then
        Insert(DbPersistedUser(PersistedUser(u.email, u.name, u.picture)))
      else
        Return
    }

    lemma /*{:_induction this}*/ ProveImplementationCorrect(u: UserInfo)
      requires PreCondition(u)
      ensures ImplementationCorrect(u)
      decreases u
    {
      assert forall before: seq<DbValue> {:trigger ExecuteProgram(before, Program(u))} :: PostCondition(u, before, Response(u), ExecuteProgram(before, Program(u))) by {
        forall before: seq<DbValue> | true
          ensures PostCondition(u, before, Response(u), ExecuteProgram(before, Program(u)))
        {
          if u.authenticated && u.email != """" {
            ghost var row := DbPersistedUser(PersistedUser(u.email, u.name, u.picture));
            assert Response(u) == Redirect(""/"");
            assert KeyOf(row) == PersistedUserKey(u.email);
            assert Program(u) == Insert(row);
            assert ProgramOperations(before, Program(u)) == [Put(row)];
            assert ExecuteProgram(before, Program(u)) == ExecuteOperations(before, [Put(row)]);
            assert ExecuteProgram(before, Program(u)) == FilterEntries(before, PersistedUserKey(u.email)) + [row];
          } else {
            assert Response(u) == ChallengeGoogle(""/save_user"");
            assert Program(u) == Return;
            assert ProgramOperations(before, Program(u)) == [];
            assert ExecuteProgram(before, Program(u)) == before;
          }
        }
      }
    }
  }
}

module DuctSecureImpl {
  function SecureHtml(ctx: UserInfo): string
    decreases ctx
  {
    var logout: string := Link(""Log out"", ""/logout"");
    var authText: string := ""You are authenticated."";
    ""<!doctype html><html lang=\""en\""><head><meta charset=\""utf-8\"" />"" + ""<meta name=\""viewport\"" content=\""width=device-width, initial-scale=1\"" />"" + ""<title>Secure</title></head><body><h1>Hello, "" + ctx.name + ""!</h1><p>"" + authText + ""</p><p>"" + logout + ""</p></body></html>""
  }

  import opened DB

  import opened DuctTools

  import opened DuctSpecs

  import opened SpecsTools

  class SecurePage extends SecurePageSpec {
    constructor ()
    {
    }

    function Response(u: UserInfo): ReturnType
      decreases u
    {
      if u.authenticated then
        Content(SecureHtml(u))
      else
        ChallengeGoogle(""/secure"")
    }

    function Program(u: UserInfo): DbProgram
      decreases u
    {
      Return
    }
  }
}

module DuctApis {

  import opened DuctTools

  import opened DuctLandingImpl

  import opened DuctLoginImpl

  import opened DuctSaveUserImpl

  import opened DuctSecureImpl
  class Views {
    static method EndPointsInterface()
    {
    }

    static method Endpoints() returns (all: AllApiEndpoints)
    {
      var catalog := new AllApiEndpoints();
      var formic_landing := new FormicLandingPage();
      var home := new ApiEndpoint(""/"", ReturnType.Content(""""), formic_landing);
      catalog.Add(home);
      var login_page := new LoginChallengePage();
      var login := new ApiEndpoint(""/login"", ReturnType.ChallengeGoogle(""/save_user""), login_page);
      catalog.Add(login);
      var save_user_page := new SaveUserPage();
      var save_user := new ApiEndpoint(""/save_user"", ReturnType.Content(""""), save_user_page);
      catalog.Add(save_user);
      var secure_page := new SecurePage();
      var secure := new ApiEndpoint(""/secure"", ReturnType.Content(""""), secure_page);
      catalog.Add(secure);
      all := catalog;
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
// end of class FuncExtensions
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
// end of class FuncExtensions
namespace DB {

  public partial class __default {
    public static DB._ITable TableOf(DB._IDbValue row) {
      DB._IDbValue _source0 = row;
      {
        if (_source0.is_DbPersistedUser) {
          return DB.Table.create_PersistedUserTable();
        }
      }
      {
        if (_source0.is_DbFormicUser) {
          return DB.Table.create_FormicUserTable();
        }
      }
      {
        if (_source0.is_DbLaunchToken) {
          return DB.Table.create_LaunchTokenTable();
        }
      }
      {
        return DB.Table.create_SessionTable();
      }
    }
    public static DB._IDbKey KeyOf(DB._IDbValue row) {
      DB._IDbValue _source0 = row;
      {
        if (_source0.is_DbPersistedUser) {
          DB._IPersistedUser _0_persistedUser = _source0.dtor_persistedUser;
          return DB.DbKey.create_PersistedUserKey((_0_persistedUser).dtor_email);
        }
      }
      {
        if (_source0.is_DbFormicUser) {
          DB._IUserCreds _1_formicUser = _source0.dtor_formicUser;
          return DB.DbKey.create_FormicUserKey((_1_formicUser).dtor_id);
        }
      }
      {
        if (_source0.is_DbLaunchToken) {
          DB._ILaunchToken _2_launchToken = _source0.dtor_launchToken;
          return DB.DbKey.create_LaunchTokenKey((_2_launchToken).dtor_id);
        }
      }
      {
        DB._ISession _3_session = _source0.dtor_session;
        return DB.DbKey.create_SessionKey((_3_session).dtor_id);
      }
    }
    public static bool ValidChange(DB._IDbChange change) {
      DB._IDbChange _source0 = change;
      {
        if (_source0.is_Put) {
          return true;
        }
      }
      {
        if (_source0.is_Edit) {
          DB._IDbKey _0_key = _source0.dtor_key;
          DB._IDbValue _1_newValue = _source0.dtor_newValue;
          return object.Equals(_0_key, DB.__default.KeyOf(_1_newValue));
        }
      }
      {
        return true;
      }
    }
    public static Dafny.ISequence<DB._IDbValue> FilterEntries(Dafny.ISequence<DB._IDbValue> entries, DB._IDbKey key)
    {
      Dafny.ISequence<DB._IDbValue> _0___accumulator = Dafny.Sequence<DB._IDbValue>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<DB._IDbValue>.Concat(_0___accumulator, Dafny.Sequence<DB._IDbValue>.FromElements());
      } else if (object.Equals(DB.__default.KeyOf((entries).Select(BigInteger.Zero)), key)) {
        Dafny.ISequence<DB._IDbValue> _in0 = (entries).Drop(BigInteger.One);
        DB._IDbKey _in1 = key;
        entries = _in0;
        key = _in1;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<DB._IDbValue>.Concat(_0___accumulator, Dafny.Sequence<DB._IDbValue>.FromElements((entries).Select(BigInteger.Zero)));
        Dafny.ISequence<DB._IDbValue> _in2 = (entries).Drop(BigInteger.One);
        DB._IDbKey _in3 = key;
        entries = _in2;
        key = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static bool HasKey(Dafny.ISequence<DB._IDbValue> entries, DB._IDbKey key)
    {
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return false;
      } else {
        return (object.Equals(DB.__default.KeyOf((entries).Select(BigInteger.Zero)), key)) || (DB.__default.HasKey((entries).Drop(BigInteger.One), key));
      }
    }
    public static bool TableHasAny(Dafny.ISequence<DB._IDbValue> entries, DB._ITable table)
    {
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return false;
      } else {
        return (object.Equals(DB.__default.TableOf((entries).Select(BigInteger.Zero)), table)) || (DB.__default.TableHasAny((entries).Drop(BigInteger.One), table));
      }
    }
    public static bool TableHasKey(Dafny.ISequence<DB._IDbValue> entries, DB._ITable table, DB._IDbKey key)
    {
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return false;
      } else {
        return ((object.Equals(DB.__default.TableOf((entries).Select(BigInteger.Zero)), table)) && (object.Equals(DB.__default.KeyOf((entries).Select(BigInteger.Zero)), key))) || (DB.__default.TableHasKey((entries).Drop(BigInteger.One), table, key));
      }
    }
    public static Dafny.ISequence<DB._IDbValue> RowsForTable(Dafny.ISequence<DB._IDbValue> entries, DB._ITable table)
    {
      Dafny.ISequence<DB._IDbValue> _0___accumulator = Dafny.Sequence<DB._IDbValue>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<DB._IDbValue>.Concat(_0___accumulator, Dafny.Sequence<DB._IDbValue>.FromElements());
      } else if (object.Equals(DB.__default.TableOf((entries).Select(BigInteger.Zero)), table)) {
        _0___accumulator = Dafny.Sequence<DB._IDbValue>.Concat(_0___accumulator, Dafny.Sequence<DB._IDbValue>.FromElements((entries).Select(BigInteger.Zero)));
        Dafny.ISequence<DB._IDbValue> _in0 = (entries).Drop(BigInteger.One);
        DB._ITable _in1 = table;
        entries = _in0;
        table = _in1;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<DB._IDbValue> _in2 = (entries).Drop(BigInteger.One);
        DB._ITable _in3 = table;
        entries = _in2;
        table = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DB._IDbValue> RowsForKey(Dafny.ISequence<DB._IDbValue> entries, DB._IDbKey key)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<DB._IDbValue>.FromElements();
      } else if (object.Equals(DB.__default.KeyOf((entries).Select(BigInteger.Zero)), key)) {
        return Dafny.Sequence<DB._IDbValue>.FromElements((entries).Select(BigInteger.Zero));
      } else {
        Dafny.ISequence<DB._IDbValue> _in0 = (entries).Drop(BigInteger.One);
        DB._IDbKey _in1 = key;
        entries = _in0;
        key = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool EvalPred(Dafny.ISequence<DB._IDbValue> entries, DB._IDbPred pred)
    {
      DB._IDbPred _source0 = pred;
      {
        if (_source0.is_TruePred) {
          return true;
        }
      }
      {
        if (_source0.is_FalsePred) {
          return false;
        }
      }
      {
        if (_source0.is_HasKeyPred) {
          DB._IDbKey _0_key = _source0.dtor_key;
          return DB.__default.HasKey(entries, _0_key);
        }
      }
      {
        if (_source0.is_TableHasAnyPred) {
          DB._ITable _1_table = _source0.dtor_table;
          return DB.__default.TableHasAny(entries, _1_table);
        }
      }
      {
        if (_source0.is_TableHasKeyPred) {
          DB._ITable _2_table = _source0.dtor_table;
          DB._IDbKey _3_key = _source0.dtor_key;
          return DB.__default.TableHasKey(entries, _2_table, _3_key);
        }
      }
      {
        if (_source0.is_NotPred) {
          DB._IDbPred _4_inner = _source0.dtor_pred;
          return !(DB.__default.EvalPred(entries, _4_inner));
        }
      }
      {
        if (_source0.is_AndPred) {
          DB._IDbPred _5_left = _source0.dtor_left;
          DB._IDbPred _6_right = _source0.dtor_right;
          return (DB.__default.EvalPred(entries, _5_left)) && (DB.__default.EvalPred(entries, _6_right));
        }
      }
      {
        DB._IDbPred _7_left = _source0.dtor_left;
        DB._IDbPred _8_right = _source0.dtor_right;
        return (DB.__default.EvalPred(entries, _7_left)) || (DB.__default.EvalPred(entries, _8_right));
      }
    }
    public static Dafny.ISequence<DB._IDbValue> EvalQuery(Dafny.ISequence<DB._IDbValue> entries, DB._IDbQuery query)
    {
      DB._IDbQuery _source0 = query;
      {
        if (_source0.is_AllRows) {
          return entries;
        }
      }
      {
        if (_source0.is_RowsInTable) {
          DB._ITable _0_table = _source0.dtor_table;
          return DB.__default.RowsForTable(entries, _0_table);
        }
      }
      {
        if (_source0.is_RowWithKey) {
          DB._IDbKey _1_key = _source0.dtor_key;
          return DB.__default.RowsForKey(entries, _1_key);
        }
      }
      {
        DB._IDbPred _2_pred = _source0.dtor_pred;
        if (DB.__default.EvalPred(entries, _2_pred)) {
          return entries;
        } else {
          return Dafny.Sequence<DB._IDbValue>.FromElements();
        }
      }
    }
    public static BigInteger ProgramSize(DB._IDbProgram program) {
      DB._IDbProgram _source0 = program;
      {
        if (_source0.is_Return) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_Seq) {
          DB._IDbProgram _0_p1 = _source0.dtor_p1;
          DB._IDbProgram _1_p2 = _source0.dtor_p2;
          return ((BigInteger.One) + (DB.__default.ProgramSize(_0_p1))) + (DB.__default.ProgramSize(_1_p2));
        }
      }
      {
        if (_source0.is_Lookup) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_Exists) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_Insert) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_Update) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_DeleteRow) {
          return BigInteger.One;
        }
      }
      {
        if (_source0.is_If) {
          DB._IDbProgram _2_thenP = _source0.dtor_thenP;
          DB._IDbProgram _3_elseP = _source0.dtor_elseP;
          return ((BigInteger.One) + (DB.__default.ProgramSize(_2_thenP))) + (DB.__default.ProgramSize(_3_elseP));
        }
      }
      {
        DB._IDbProgram _4_body = _source0.dtor_body;
        return (BigInteger.One) + (DB.__default.ProgramSize(_4_body));
      }
    }
    public static Dafny.ISequence<DB._IDbChange> PatchToChange(DB._IDbKey key, DB._IDbValue patch)
    {
      DB._IDbValue _source0 = patch;
      {
        DB._IDbValue _0_row = _source0;
        if (object.Equals(DB.__default.KeyOf(_0_row), key)) {
          return Dafny.Sequence<DB._IDbChange>.FromElements(DB.DbChange.create_Edit(key, _0_row));
        } else {
          return Dafny.Sequence<DB._IDbChange>.FromElements();
        }
      }
    }
    public static Dafny.ISequence<DB._IDbValue> ExecuteOperation(Dafny.ISequence<DB._IDbValue> entries, DB._IDbChange change)
    {
      DB._IDbChange _source0 = change;
      {
        if (_source0.is_Put) {
          DB._IDbValue _0_row = _source0.dtor_row;
          return Dafny.Sequence<DB._IDbValue>.Concat(DB.__default.FilterEntries(entries, DB.__default.KeyOf(_0_row)), Dafny.Sequence<DB._IDbValue>.FromElements(_0_row));
        }
      }
      {
        if (_source0.is_Edit) {
          DB._IDbKey _1_key = _source0.dtor_key;
          DB._IDbValue _2_newValue = _source0.dtor_newValue;
          if (object.Equals(_1_key, DB.__default.KeyOf(_2_newValue))) {
            return Dafny.Sequence<DB._IDbValue>.Concat(DB.__default.FilterEntries(entries, _1_key), Dafny.Sequence<DB._IDbValue>.FromElements(_2_newValue));
          } else {
            return entries;
          }
        }
      }
      {
        DB._IDbKey _3_key = _source0.dtor_key;
        return DB.__default.FilterEntries(entries, _3_key);
      }
    }
    public static Dafny.ISequence<DB._IDbValue> ExecuteOperations(Dafny.ISequence<DB._IDbValue> entries, Dafny.ISequence<DB._IDbChange> changes)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((changes).Count)).Sign == 0) {
        return entries;
      } else {
        Dafny.ISequence<DB._IDbValue> _in0 = DB.__default.ExecuteOperation(entries, (changes).Select(BigInteger.Zero));
        Dafny.ISequence<DB._IDbChange> _in1 = (changes).Drop(BigInteger.One);
        entries = _in0;
        changes = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DB._IDbChange> ProgramOperationsForRows(Dafny.ISequence<DB._IDbValue> entries, Dafny.ISequence<DB._IDbValue> rows, DB._IDbProgram body)
    {
      if ((new BigInteger((rows).Count)).Sign == 0) {
        return Dafny.Sequence<DB._IDbChange>.FromElements();
      } else {
        Dafny.ISequence<DB._IDbChange> _0_ops = DB.__default.ProgramOperations(entries, body);
        return Dafny.Sequence<DB._IDbChange>.Concat(_0_ops, DB.__default.ProgramOperationsForRows(DB.__default.ExecuteOperations(entries, _0_ops), (rows).Drop(BigInteger.One), body));
      }
    }
    public static Dafny.ISequence<DB._IDbChange> ProgramOperations(Dafny.ISequence<DB._IDbValue> entries, DB._IDbProgram program)
    {
      DB._IDbProgram _source0 = program;
      {
        if (_source0.is_Return) {
          return Dafny.Sequence<DB._IDbChange>.FromElements();
        }
      }
      {
        if (_source0.is_Seq) {
          DB._IDbProgram _0_p1 = _source0.dtor_p1;
          DB._IDbProgram _1_p2 = _source0.dtor_p2;
          Dafny.ISequence<DB._IDbChange> _2_ops1 = DB.__default.ProgramOperations(entries, _0_p1);
          return Dafny.Sequence<DB._IDbChange>.Concat(_2_ops1, DB.__default.ProgramOperations(DB.__default.ExecuteOperations(entries, _2_ops1), _1_p2));
        }
      }
      {
        if (_source0.is_Lookup) {
          return Dafny.Sequence<DB._IDbChange>.FromElements();
        }
      }
      {
        if (_source0.is_Exists) {
          return Dafny.Sequence<DB._IDbChange>.FromElements();
        }
      }
      {
        if (_source0.is_Insert) {
          DB._IDbValue _3_row = _source0.dtor_row;
          return Dafny.Sequence<DB._IDbChange>.FromElements(DB.DbChange.create_Put(_3_row));
        }
      }
      {
        if (_source0.is_Update) {
          DB._IDbKey _4_key = _source0.dtor_key;
          DB._IDbValue _5_patch = _source0.dtor_patch;
          return DB.__default.PatchToChange(_4_key, _5_patch);
        }
      }
      {
        if (_source0.is_DeleteRow) {
          DB._IDbKey _6_key = _source0.dtor_key;
          return Dafny.Sequence<DB._IDbChange>.FromElements(DB.DbChange.create_Delete(_6_key));
        }
      }
      {
        if (_source0.is_If) {
          DB._IDbPred _7_cond = _source0.dtor_cond;
          DB._IDbProgram _8_thenP = _source0.dtor_thenP;
          DB._IDbProgram _9_elseP = _source0.dtor_elseP;
          if (DB.__default.EvalPred(entries, _7_cond)) {
            return DB.__default.ProgramOperations(entries, _8_thenP);
          } else {
            return DB.__default.ProgramOperations(entries, _9_elseP);
          }
        }
      }
      {
        DB._IDbQuery _10_query = _source0.dtor_query;
        DB._IDbProgram _11_body = _source0.dtor_body;
        return DB.__default.ProgramOperationsForRows(entries, DB.__default.EvalQuery(entries, _10_query), _11_body);
      }
    }
    public static Dafny.ISequence<DB._IDbValue> ExecuteProgram(Dafny.ISequence<DB._IDbValue> entries, DB._IDbProgram program)
    {
      return DB.__default.ExecuteOperations(entries, DB.__default.ProgramOperations(entries, program));
    }
  }

  public interface _IDbTimestamp {
    bool is_DbTimestamp { get; }
    Dafny.ISequence<Dafny.Rune> dtor_value { get; }
  }
  public class DbTimestamp : _IDbTimestamp {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public DbTimestamp(Dafny.ISequence<Dafny.Rune> @value) {
      this._value = @value;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbTimestamp;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbTimestamp.DbTimestamp";
      s += "(";
      s += this._value.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly Dafny.ISequence<Dafny.Rune> theDefault = Dafny.Sequence<Dafny.Rune>.Empty;
    public static Dafny.ISequence<Dafny.Rune> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbTimestamp create(Dafny.ISequence<Dafny.Rune> @value) {
      return new DbTimestamp(@value);
    }
    public static _IDbTimestamp create_DbTimestamp(Dafny.ISequence<Dafny.Rune> @value) {
      return create(@value);
    }
    public bool is_DbTimestamp { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_value {
      get {
        return this._value;
      }
    }
  }

  public interface _IOptionalDbTimestamp {
    bool is_MissingTimestamp { get; }
    bool is_PresentTimestamp { get; }
    Dafny.ISequence<Dafny.Rune> dtor_value { get; }
    _IOptionalDbTimestamp DowncastClone();
  }
  public abstract class OptionalDbTimestamp : _IOptionalDbTimestamp {
    public OptionalDbTimestamp() {
    }
    private static readonly DB._IOptionalDbTimestamp theDefault = create_MissingTimestamp();
    public static DB._IOptionalDbTimestamp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IOptionalDbTimestamp> _TYPE = new Dafny.TypeDescriptor<DB._IOptionalDbTimestamp>(DB.OptionalDbTimestamp.Default());
    public static Dafny.TypeDescriptor<DB._IOptionalDbTimestamp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOptionalDbTimestamp create_MissingTimestamp() {
      return new OptionalDbTimestamp_MissingTimestamp();
    }
    public static _IOptionalDbTimestamp create_PresentTimestamp(Dafny.ISequence<Dafny.Rune> @value) {
      return new OptionalDbTimestamp_PresentTimestamp(@value);
    }
    public bool is_MissingTimestamp { get { return this is OptionalDbTimestamp_MissingTimestamp; } }
    public bool is_PresentTimestamp { get { return this is OptionalDbTimestamp_PresentTimestamp; } }
    public Dafny.ISequence<Dafny.Rune> dtor_value {
      get {
        var d = this;
        return ((OptionalDbTimestamp_PresentTimestamp)d)._value;
      }
    }
    public abstract _IOptionalDbTimestamp DowncastClone();
  }
  public class OptionalDbTimestamp_MissingTimestamp : OptionalDbTimestamp {
    public OptionalDbTimestamp_MissingTimestamp() : base() {
    }
    public override _IOptionalDbTimestamp DowncastClone() {
      if (this is _IOptionalDbTimestamp dt) { return dt; }
      return new OptionalDbTimestamp_MissingTimestamp();
    }
    public override bool Equals(object other) {
      var oth = other as DB.OptionalDbTimestamp_MissingTimestamp;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.OptionalDbTimestamp.MissingTimestamp";
      return s;
    }
  }
  public class OptionalDbTimestamp_PresentTimestamp : OptionalDbTimestamp {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public OptionalDbTimestamp_PresentTimestamp(Dafny.ISequence<Dafny.Rune> @value) : base() {
      this._value = @value;
    }
    public override _IOptionalDbTimestamp DowncastClone() {
      if (this is _IOptionalDbTimestamp dt) { return dt; }
      return new OptionalDbTimestamp_PresentTimestamp(_value);
    }
    public override bool Equals(object other) {
      var oth = other as DB.OptionalDbTimestamp_PresentTimestamp;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.OptionalDbTimestamp.PresentTimestamp";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }

  public interface _IPersistedUser {
    bool is_PersistedUser { get; }
    Dafny.ISequence<Dafny.Rune> dtor_email { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_picture { get; }
    _IPersistedUser DowncastClone();
  }
  public class PersistedUser : _IPersistedUser {
    public readonly Dafny.ISequence<Dafny.Rune> _email;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _picture;
    public PersistedUser(Dafny.ISequence<Dafny.Rune> email, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> picture) {
      this._email = email;
      this._name = name;
      this._picture = picture;
    }
    public _IPersistedUser DowncastClone() {
      if (this is _IPersistedUser dt) { return dt; }
      return new PersistedUser(_email, _name, _picture);
    }
    public override bool Equals(object other) {
      var oth = other as DB.PersistedUser;
      return oth != null && object.Equals(this._email, oth._email) && object.Equals(this._name, oth._name) && object.Equals(this._picture, oth._picture);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._email));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._picture));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.PersistedUser.PersistedUser";
      s += "(";
      s += this._email.ToVerbatimString(true);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += this._picture.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly DB._IPersistedUser theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty);
    public static DB._IPersistedUser Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IPersistedUser> _TYPE = new Dafny.TypeDescriptor<DB._IPersistedUser>(DB.PersistedUser.Default());
    public static Dafny.TypeDescriptor<DB._IPersistedUser> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPersistedUser create(Dafny.ISequence<Dafny.Rune> email, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> picture) {
      return new PersistedUser(email, name, picture);
    }
    public static _IPersistedUser create_PersistedUser(Dafny.ISequence<Dafny.Rune> email, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> picture) {
      return create(email, name, picture);
    }
    public bool is_PersistedUser { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_email {
      get {
        return this._email;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_picture {
      get {
        return this._picture;
      }
    }
  }

  public interface _IUserCreds {
    bool is_FormicUser { get; }
    BigInteger dtor_id { get; }
    DB._IPersistedUser dtor_user { get; }
    DB._ILaunchToken dtor_launch__token { get; }
    _IUserCreds DowncastClone();
  }
  public class UserCreds : _IUserCreds {
    public readonly BigInteger _id;
    public readonly DB._IPersistedUser _user;
    public readonly DB._ILaunchToken _launch__token;
    public UserCreds(BigInteger id, DB._IPersistedUser user, DB._ILaunchToken launch__token) {
      this._id = id;
      this._user = user;
      this._launch__token = launch__token;
    }
    public _IUserCreds DowncastClone() {
      if (this is _IUserCreds dt) { return dt; }
      return new UserCreds(_id, _user, _launch__token);
    }
    public override bool Equals(object other) {
      var oth = other as DB.UserCreds;
      return oth != null && this._id == oth._id && object.Equals(this._user, oth._user) && object.Equals(this._launch__token, oth._launch__token);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._user));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._launch__token));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.UserCreds.FormicUser";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._user);
      s += ", ";
      s += Dafny.Helpers.ToString(this._launch__token);
      s += ")";
      return s;
    }
    private static readonly DB._IUserCreds theDefault = create(BigInteger.Zero, DB.PersistedUser.Default(), DB.LaunchToken.Default());
    public static DB._IUserCreds Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IUserCreds> _TYPE = new Dafny.TypeDescriptor<DB._IUserCreds>(DB.UserCreds.Default());
    public static Dafny.TypeDescriptor<DB._IUserCreds> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUserCreds create(BigInteger id, DB._IPersistedUser user, DB._ILaunchToken launch__token) {
      return new UserCreds(id, user, launch__token);
    }
    public static _IUserCreds create_FormicUser(BigInteger id, DB._IPersistedUser user, DB._ILaunchToken launch__token) {
      return create(id, user, launch__token);
    }
    public bool is_FormicUser { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public DB._IPersistedUser dtor_user {
      get {
        return this._user;
      }
    }
    public DB._ILaunchToken dtor_launch__token {
      get {
        return this._launch__token;
      }
    }
  }

  public interface _ILaunchToken {
    bool is_LaunchToken { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_user__id { get; }
    Dafny.ISequence<Dafny.Rune> dtor_token__hash { get; }
    Dafny.ISequence<Dafny.Rune> dtor_expires__at { get; }
    DB._IOptionalDbTimestamp dtor_used__at { get; }
    Dafny.ISequence<Dafny.Rune> dtor_created__at { get; }
    _ILaunchToken DowncastClone();
  }
  public class LaunchToken : _ILaunchToken {
    public readonly BigInteger _id;
    public readonly BigInteger _user__id;
    public readonly Dafny.ISequence<Dafny.Rune> _token__hash;
    public readonly Dafny.ISequence<Dafny.Rune> _expires__at;
    public readonly DB._IOptionalDbTimestamp _used__at;
    public readonly Dafny.ISequence<Dafny.Rune> _created__at;
    public LaunchToken(BigInteger id, BigInteger user__id, Dafny.ISequence<Dafny.Rune> token__hash, Dafny.ISequence<Dafny.Rune> expires__at, DB._IOptionalDbTimestamp used__at, Dafny.ISequence<Dafny.Rune> created__at) {
      this._id = id;
      this._user__id = user__id;
      this._token__hash = token__hash;
      this._expires__at = expires__at;
      this._used__at = used__at;
      this._created__at = created__at;
    }
    public _ILaunchToken DowncastClone() {
      if (this is _ILaunchToken dt) { return dt; }
      return new LaunchToken(_id, _user__id, _token__hash, _expires__at, _used__at, _created__at);
    }
    public override bool Equals(object other) {
      var oth = other as DB.LaunchToken;
      return oth != null && this._id == oth._id && this._user__id == oth._user__id && object.Equals(this._token__hash, oth._token__hash) && object.Equals(this._expires__at, oth._expires__at) && object.Equals(this._used__at, oth._used__at) && object.Equals(this._created__at, oth._created__at);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._user__id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._token__hash));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expires__at));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._used__at));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._created__at));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.LaunchToken.LaunchToken";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._user__id);
      s += ", ";
      s += this._token__hash.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expires__at);
      s += ", ";
      s += Dafny.Helpers.ToString(this._used__at);
      s += ", ";
      s += Dafny.Helpers.ToString(this._created__at);
      s += ")";
      return s;
    }
    private static readonly DB._ILaunchToken theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, DB.OptionalDbTimestamp.Default(), Dafny.Sequence<Dafny.Rune>.Empty);
    public static DB._ILaunchToken Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._ILaunchToken> _TYPE = new Dafny.TypeDescriptor<DB._ILaunchToken>(DB.LaunchToken.Default());
    public static Dafny.TypeDescriptor<DB._ILaunchToken> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ILaunchToken create(BigInteger id, BigInteger user__id, Dafny.ISequence<Dafny.Rune> token__hash, Dafny.ISequence<Dafny.Rune> expires__at, DB._IOptionalDbTimestamp used__at, Dafny.ISequence<Dafny.Rune> created__at) {
      return new LaunchToken(id, user__id, token__hash, expires__at, used__at, created__at);
    }
    public static _ILaunchToken create_LaunchToken(BigInteger id, BigInteger user__id, Dafny.ISequence<Dafny.Rune> token__hash, Dafny.ISequence<Dafny.Rune> expires__at, DB._IOptionalDbTimestamp used__at, Dafny.ISequence<Dafny.Rune> created__at) {
      return create(id, user__id, token__hash, expires__at, used__at, created__at);
    }
    public bool is_LaunchToken { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_user__id {
      get {
        return this._user__id;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_token__hash {
      get {
        return this._token__hash;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_expires__at {
      get {
        return this._expires__at;
      }
    }
    public DB._IOptionalDbTimestamp dtor_used__at {
      get {
        return this._used__at;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_created__at {
      get {
        return this._created__at;
      }
    }
  }

  public interface _ISession {
    bool is_Session { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_user__id { get; }
    Dafny.ISequence<Dafny.Rune> dtor_token__hash { get; }
    Dafny.ISequence<Dafny.Rune> dtor_expires__at { get; }
    DB._IOptionalDbTimestamp dtor_revoked__at { get; }
    Dafny.ISequence<Dafny.Rune> dtor_created__at { get; }
    Dafny.ISequence<Dafny.Rune> dtor_last__seen__at { get; }
    _ISession DowncastClone();
  }
  public class Session : _ISession {
    public readonly BigInteger _id;
    public readonly BigInteger _user__id;
    public readonly Dafny.ISequence<Dafny.Rune> _token__hash;
    public readonly Dafny.ISequence<Dafny.Rune> _expires__at;
    public readonly DB._IOptionalDbTimestamp _revoked__at;
    public readonly Dafny.ISequence<Dafny.Rune> _created__at;
    public readonly Dafny.ISequence<Dafny.Rune> _last__seen__at;
    public Session(BigInteger id, BigInteger user__id, Dafny.ISequence<Dafny.Rune> token__hash, Dafny.ISequence<Dafny.Rune> expires__at, DB._IOptionalDbTimestamp revoked__at, Dafny.ISequence<Dafny.Rune> created__at, Dafny.ISequence<Dafny.Rune> last__seen__at) {
      this._id = id;
      this._user__id = user__id;
      this._token__hash = token__hash;
      this._expires__at = expires__at;
      this._revoked__at = revoked__at;
      this._created__at = created__at;
      this._last__seen__at = last__seen__at;
    }
    public _ISession DowncastClone() {
      if (this is _ISession dt) { return dt; }
      return new Session(_id, _user__id, _token__hash, _expires__at, _revoked__at, _created__at, _last__seen__at);
    }
    public override bool Equals(object other) {
      var oth = other as DB.Session;
      return oth != null && this._id == oth._id && this._user__id == oth._user__id && object.Equals(this._token__hash, oth._token__hash) && object.Equals(this._expires__at, oth._expires__at) && object.Equals(this._revoked__at, oth._revoked__at) && object.Equals(this._created__at, oth._created__at) && object.Equals(this._last__seen__at, oth._last__seen__at);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._user__id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._token__hash));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expires__at));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._revoked__at));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._created__at));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._last__seen__at));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.Session.Session";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._user__id);
      s += ", ";
      s += this._token__hash.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expires__at);
      s += ", ";
      s += Dafny.Helpers.ToString(this._revoked__at);
      s += ", ";
      s += Dafny.Helpers.ToString(this._created__at);
      s += ", ";
      s += Dafny.Helpers.ToString(this._last__seen__at);
      s += ")";
      return s;
    }
    private static readonly DB._ISession theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, DB.OptionalDbTimestamp.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty);
    public static DB._ISession Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._ISession> _TYPE = new Dafny.TypeDescriptor<DB._ISession>(DB.Session.Default());
    public static Dafny.TypeDescriptor<DB._ISession> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISession create(BigInteger id, BigInteger user__id, Dafny.ISequence<Dafny.Rune> token__hash, Dafny.ISequence<Dafny.Rune> expires__at, DB._IOptionalDbTimestamp revoked__at, Dafny.ISequence<Dafny.Rune> created__at, Dafny.ISequence<Dafny.Rune> last__seen__at) {
      return new Session(id, user__id, token__hash, expires__at, revoked__at, created__at, last__seen__at);
    }
    public static _ISession create_Session(BigInteger id, BigInteger user__id, Dafny.ISequence<Dafny.Rune> token__hash, Dafny.ISequence<Dafny.Rune> expires__at, DB._IOptionalDbTimestamp revoked__at, Dafny.ISequence<Dafny.Rune> created__at, Dafny.ISequence<Dafny.Rune> last__seen__at) {
      return create(id, user__id, token__hash, expires__at, revoked__at, created__at, last__seen__at);
    }
    public bool is_Session { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_user__id {
      get {
        return this._user__id;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_token__hash {
      get {
        return this._token__hash;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_expires__at {
      get {
        return this._expires__at;
      }
    }
    public DB._IOptionalDbTimestamp dtor_revoked__at {
      get {
        return this._revoked__at;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_created__at {
      get {
        return this._created__at;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_last__seen__at {
      get {
        return this._last__seen__at;
      }
    }
  }

  public interface _ITable {
    bool is_PersistedUserTable { get; }
    bool is_FormicUserTable { get; }
    bool is_LaunchTokenTable { get; }
    bool is_SessionTable { get; }
    _ITable DowncastClone();
  }
  public abstract class Table : _ITable {
    public Table() {
    }
    private static readonly DB._ITable theDefault = create_PersistedUserTable();
    public static DB._ITable Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._ITable> _TYPE = new Dafny.TypeDescriptor<DB._ITable>(DB.Table.Default());
    public static Dafny.TypeDescriptor<DB._ITable> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITable create_PersistedUserTable() {
      return new Table_PersistedUserTable();
    }
    public static _ITable create_FormicUserTable() {
      return new Table_FormicUserTable();
    }
    public static _ITable create_LaunchTokenTable() {
      return new Table_LaunchTokenTable();
    }
    public static _ITable create_SessionTable() {
      return new Table_SessionTable();
    }
    public bool is_PersistedUserTable { get { return this is Table_PersistedUserTable; } }
    public bool is_FormicUserTable { get { return this is Table_FormicUserTable; } }
    public bool is_LaunchTokenTable { get { return this is Table_LaunchTokenTable; } }
    public bool is_SessionTable { get { return this is Table_SessionTable; } }
    public static System.Collections.Generic.IEnumerable<_ITable> AllSingletonConstructors {
      get {
        yield return Table.create_PersistedUserTable();
        yield return Table.create_FormicUserTable();
        yield return Table.create_LaunchTokenTable();
        yield return Table.create_SessionTable();
      }
    }
    public abstract _ITable DowncastClone();
  }
  public class Table_PersistedUserTable : Table {
    public Table_PersistedUserTable() : base() {
    }
    public override _ITable DowncastClone() {
      if (this is _ITable dt) { return dt; }
      return new Table_PersistedUserTable();
    }
    public override bool Equals(object other) {
      var oth = other as DB.Table_PersistedUserTable;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.Table.PersistedUserTable";
      return s;
    }
  }
  public class Table_FormicUserTable : Table {
    public Table_FormicUserTable() : base() {
    }
    public override _ITable DowncastClone() {
      if (this is _ITable dt) { return dt; }
      return new Table_FormicUserTable();
    }
    public override bool Equals(object other) {
      var oth = other as DB.Table_FormicUserTable;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.Table.FormicUserTable";
      return s;
    }
  }
  public class Table_LaunchTokenTable : Table {
    public Table_LaunchTokenTable() : base() {
    }
    public override _ITable DowncastClone() {
      if (this is _ITable dt) { return dt; }
      return new Table_LaunchTokenTable();
    }
    public override bool Equals(object other) {
      var oth = other as DB.Table_LaunchTokenTable;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.Table.LaunchTokenTable";
      return s;
    }
  }
  public class Table_SessionTable : Table {
    public Table_SessionTable() : base() {
    }
    public override _ITable DowncastClone() {
      if (this is _ITable dt) { return dt; }
      return new Table_SessionTable();
    }
    public override bool Equals(object other) {
      var oth = other as DB.Table_SessionTable;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.Table.SessionTable";
      return s;
    }
  }

  public interface _IDbValue {
    bool is_DbPersistedUser { get; }
    bool is_DbFormicUser { get; }
    bool is_DbLaunchToken { get; }
    bool is_DbSession { get; }
    DB._IPersistedUser dtor_persistedUser { get; }
    DB._IUserCreds dtor_formicUser { get; }
    DB._ILaunchToken dtor_launchToken { get; }
    DB._ISession dtor_session { get; }
    _IDbValue DowncastClone();
  }
  public abstract class DbValue : _IDbValue {
    public DbValue() {
    }
    private static readonly DB._IDbValue theDefault = create_DbPersistedUser(DB.PersistedUser.Default());
    public static DB._IDbValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbValue> _TYPE = new Dafny.TypeDescriptor<DB._IDbValue>(DB.DbValue.Default());
    public static Dafny.TypeDescriptor<DB._IDbValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbValue create_DbPersistedUser(DB._IPersistedUser persistedUser) {
      return new DbValue_DbPersistedUser(persistedUser);
    }
    public static _IDbValue create_DbFormicUser(DB._IUserCreds formicUser) {
      return new DbValue_DbFormicUser(formicUser);
    }
    public static _IDbValue create_DbLaunchToken(DB._ILaunchToken launchToken) {
      return new DbValue_DbLaunchToken(launchToken);
    }
    public static _IDbValue create_DbSession(DB._ISession session) {
      return new DbValue_DbSession(session);
    }
    public bool is_DbPersistedUser { get { return this is DbValue_DbPersistedUser; } }
    public bool is_DbFormicUser { get { return this is DbValue_DbFormicUser; } }
    public bool is_DbLaunchToken { get { return this is DbValue_DbLaunchToken; } }
    public bool is_DbSession { get { return this is DbValue_DbSession; } }
    public DB._IPersistedUser dtor_persistedUser {
      get {
        var d = this;
        return ((DbValue_DbPersistedUser)d)._persistedUser;
      }
    }
    public DB._IUserCreds dtor_formicUser {
      get {
        var d = this;
        return ((DbValue_DbFormicUser)d)._formicUser;
      }
    }
    public DB._ILaunchToken dtor_launchToken {
      get {
        var d = this;
        return ((DbValue_DbLaunchToken)d)._launchToken;
      }
    }
    public DB._ISession dtor_session {
      get {
        var d = this;
        return ((DbValue_DbSession)d)._session;
      }
    }
    public abstract _IDbValue DowncastClone();
  }
  public class DbValue_DbPersistedUser : DbValue {
    public readonly DB._IPersistedUser _persistedUser;
    public DbValue_DbPersistedUser(DB._IPersistedUser persistedUser) : base() {
      this._persistedUser = persistedUser;
    }
    public override _IDbValue DowncastClone() {
      if (this is _IDbValue dt) { return dt; }
      return new DbValue_DbPersistedUser(_persistedUser);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbValue_DbPersistedUser;
      return oth != null && object.Equals(this._persistedUser, oth._persistedUser);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._persistedUser));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbValue.DbPersistedUser";
      s += "(";
      s += Dafny.Helpers.ToString(this._persistedUser);
      s += ")";
      return s;
    }
  }
  public class DbValue_DbFormicUser : DbValue {
    public readonly DB._IUserCreds _formicUser;
    public DbValue_DbFormicUser(DB._IUserCreds formicUser) : base() {
      this._formicUser = formicUser;
    }
    public override _IDbValue DowncastClone() {
      if (this is _IDbValue dt) { return dt; }
      return new DbValue_DbFormicUser(_formicUser);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbValue_DbFormicUser;
      return oth != null && object.Equals(this._formicUser, oth._formicUser);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formicUser));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbValue.DbFormicUser";
      s += "(";
      s += Dafny.Helpers.ToString(this._formicUser);
      s += ")";
      return s;
    }
  }
  public class DbValue_DbLaunchToken : DbValue {
    public readonly DB._ILaunchToken _launchToken;
    public DbValue_DbLaunchToken(DB._ILaunchToken launchToken) : base() {
      this._launchToken = launchToken;
    }
    public override _IDbValue DowncastClone() {
      if (this is _IDbValue dt) { return dt; }
      return new DbValue_DbLaunchToken(_launchToken);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbValue_DbLaunchToken;
      return oth != null && object.Equals(this._launchToken, oth._launchToken);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._launchToken));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbValue.DbLaunchToken";
      s += "(";
      s += Dafny.Helpers.ToString(this._launchToken);
      s += ")";
      return s;
    }
  }
  public class DbValue_DbSession : DbValue {
    public readonly DB._ISession _session;
    public DbValue_DbSession(DB._ISession session) : base() {
      this._session = session;
    }
    public override _IDbValue DowncastClone() {
      if (this is _IDbValue dt) { return dt; }
      return new DbValue_DbSession(_session);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbValue_DbSession;
      return oth != null && object.Equals(this._session, oth._session);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._session));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbValue.DbSession";
      s += "(";
      s += Dafny.Helpers.ToString(this._session);
      s += ")";
      return s;
    }
  }

  public interface _IDbKey {
    bool is_PersistedUserKey { get; }
    bool is_FormicUserKey { get; }
    bool is_LaunchTokenKey { get; }
    bool is_SessionKey { get; }
    Dafny.ISequence<Dafny.Rune> dtor_email { get; }
    BigInteger dtor_id { get; }
    _IDbKey DowncastClone();
  }
  public abstract class DbKey : _IDbKey {
    public DbKey() {
    }
    private static readonly DB._IDbKey theDefault = create_PersistedUserKey(Dafny.Sequence<Dafny.Rune>.Empty);
    public static DB._IDbKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbKey> _TYPE = new Dafny.TypeDescriptor<DB._IDbKey>(DB.DbKey.Default());
    public static Dafny.TypeDescriptor<DB._IDbKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbKey create_PersistedUserKey(Dafny.ISequence<Dafny.Rune> email) {
      return new DbKey_PersistedUserKey(email);
    }
    public static _IDbKey create_FormicUserKey(BigInteger id) {
      return new DbKey_FormicUserKey(id);
    }
    public static _IDbKey create_LaunchTokenKey(BigInteger id) {
      return new DbKey_LaunchTokenKey(id);
    }
    public static _IDbKey create_SessionKey(BigInteger id) {
      return new DbKey_SessionKey(id);
    }
    public bool is_PersistedUserKey { get { return this is DbKey_PersistedUserKey; } }
    public bool is_FormicUserKey { get { return this is DbKey_FormicUserKey; } }
    public bool is_LaunchTokenKey { get { return this is DbKey_LaunchTokenKey; } }
    public bool is_SessionKey { get { return this is DbKey_SessionKey; } }
    public Dafny.ISequence<Dafny.Rune> dtor_email {
      get {
        var d = this;
        return ((DbKey_PersistedUserKey)d)._email;
      }
    }
    public BigInteger dtor_id {
      get {
        var d = this;
        if (d is DbKey_FormicUserKey) { return ((DbKey_FormicUserKey)d)._id; }
        if (d is DbKey_LaunchTokenKey) { return ((DbKey_LaunchTokenKey)d)._id; }
        return ((DbKey_SessionKey)d)._id;
      }
    }
    public abstract _IDbKey DowncastClone();
  }
  public class DbKey_PersistedUserKey : DbKey {
    public readonly Dafny.ISequence<Dafny.Rune> _email;
    public DbKey_PersistedUserKey(Dafny.ISequence<Dafny.Rune> email) : base() {
      this._email = email;
    }
    public override _IDbKey DowncastClone() {
      if (this is _IDbKey dt) { return dt; }
      return new DbKey_PersistedUserKey(_email);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbKey_PersistedUserKey;
      return oth != null && object.Equals(this._email, oth._email);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._email));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbKey.PersistedUserKey";
      s += "(";
      s += this._email.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class DbKey_FormicUserKey : DbKey {
    public readonly BigInteger _id;
    public DbKey_FormicUserKey(BigInteger id) : base() {
      this._id = id;
    }
    public override _IDbKey DowncastClone() {
      if (this is _IDbKey dt) { return dt; }
      return new DbKey_FormicUserKey(_id);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbKey_FormicUserKey;
      return oth != null && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbKey.FormicUserKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }
  public class DbKey_LaunchTokenKey : DbKey {
    public readonly BigInteger _id;
    public DbKey_LaunchTokenKey(BigInteger id) : base() {
      this._id = id;
    }
    public override _IDbKey DowncastClone() {
      if (this is _IDbKey dt) { return dt; }
      return new DbKey_LaunchTokenKey(_id);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbKey_LaunchTokenKey;
      return oth != null && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbKey.LaunchTokenKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }
  public class DbKey_SessionKey : DbKey {
    public readonly BigInteger _id;
    public DbKey_SessionKey(BigInteger id) : base() {
      this._id = id;
    }
    public override _IDbKey DowncastClone() {
      if (this is _IDbKey dt) { return dt; }
      return new DbKey_SessionKey(_id);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbKey_SessionKey;
      return oth != null && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbKey.SessionKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }

  public interface _IDbChange {
    bool is_Put { get; }
    bool is_Edit { get; }
    bool is_Delete { get; }
    DB._IDbValue dtor_row { get; }
    DB._IDbKey dtor_key { get; }
    DB._IDbValue dtor_newValue { get; }
    _IDbChange DowncastClone();
  }
  public abstract class DbChange : _IDbChange {
    public DbChange() {
    }
    private static readonly DB._IDbChange theDefault = create_Put(DB.DbValue.Default());
    public static DB._IDbChange Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbChange> _TYPE = new Dafny.TypeDescriptor<DB._IDbChange>(DB.DbChange.Default());
    public static Dafny.TypeDescriptor<DB._IDbChange> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbChange create_Put(DB._IDbValue row) {
      return new DbChange_Put(row);
    }
    public static _IDbChange create_Edit(DB._IDbKey key, DB._IDbValue newValue) {
      return new DbChange_Edit(key, newValue);
    }
    public static _IDbChange create_Delete(DB._IDbKey key) {
      return new DbChange_Delete(key);
    }
    public bool is_Put { get { return this is DbChange_Put; } }
    public bool is_Edit { get { return this is DbChange_Edit; } }
    public bool is_Delete { get { return this is DbChange_Delete; } }
    public DB._IDbValue dtor_row {
      get {
        var d = this;
        return ((DbChange_Put)d)._row;
      }
    }
    public DB._IDbKey dtor_key {
      get {
        var d = this;
        if (d is DbChange_Edit) { return ((DbChange_Edit)d)._key; }
        return ((DbChange_Delete)d)._key;
      }
    }
    public DB._IDbValue dtor_newValue {
      get {
        var d = this;
        return ((DbChange_Edit)d)._newValue;
      }
    }
    public abstract _IDbChange DowncastClone();
  }
  public class DbChange_Put : DbChange {
    public readonly DB._IDbValue _row;
    public DbChange_Put(DB._IDbValue row) : base() {
      this._row = row;
    }
    public override _IDbChange DowncastClone() {
      if (this is _IDbChange dt) { return dt; }
      return new DbChange_Put(_row);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbChange_Put;
      return oth != null && object.Equals(this._row, oth._row);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._row));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbChange.Put";
      s += "(";
      s += Dafny.Helpers.ToString(this._row);
      s += ")";
      return s;
    }
  }
  public class DbChange_Edit : DbChange {
    public readonly DB._IDbKey _key;
    public readonly DB._IDbValue _newValue;
    public DbChange_Edit(DB._IDbKey key, DB._IDbValue newValue) : base() {
      this._key = key;
      this._newValue = newValue;
    }
    public override _IDbChange DowncastClone() {
      if (this is _IDbChange dt) { return dt; }
      return new DbChange_Edit(_key, _newValue);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbChange_Edit;
      return oth != null && object.Equals(this._key, oth._key) && object.Equals(this._newValue, oth._newValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbChange.Edit";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newValue);
      s += ")";
      return s;
    }
  }
  public class DbChange_Delete : DbChange {
    public readonly DB._IDbKey _key;
    public DbChange_Delete(DB._IDbKey key) : base() {
      this._key = key;
    }
    public override _IDbChange DowncastClone() {
      if (this is _IDbChange dt) { return dt; }
      return new DbChange_Delete(_key);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbChange_Delete;
      return oth != null && object.Equals(this._key, oth._key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbChange.Delete";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ")";
      return s;
    }
  }

  public interface _IPatch {
    bool is_ReplaceWith { get; }
    DB._IDbValue dtor_row { get; }
  }
  public class Patch : _IPatch {
    public readonly DB._IDbValue _row;
    public Patch(DB._IDbValue row) {
      this._row = row;
    }
    public static DB._IDbValue DowncastClone(DB._IDbValue _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DB.Patch;
      return oth != null && object.Equals(this._row, oth._row);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._row));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.Patch.ReplaceWith";
      s += "(";
      s += Dafny.Helpers.ToString(this._row);
      s += ")";
      return s;
    }
    private static readonly DB._IDbValue theDefault = DB.DbValue.Default();
    public static DB._IDbValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbValue> _TYPE = new Dafny.TypeDescriptor<DB._IDbValue>(DB.DbValue.Default());
    public static Dafny.TypeDescriptor<DB._IDbValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPatch create(DB._IDbValue row) {
      return new Patch(row);
    }
    public static _IPatch create_ReplaceWith(DB._IDbValue row) {
      return create(row);
    }
    public bool is_ReplaceWith { get { return true; } }
    public DB._IDbValue dtor_row {
      get {
        return this._row;
      }
    }
  }

  public interface _IDbPred {
    bool is_TruePred { get; }
    bool is_FalsePred { get; }
    bool is_HasKeyPred { get; }
    bool is_TableHasAnyPred { get; }
    bool is_TableHasKeyPred { get; }
    bool is_NotPred { get; }
    bool is_AndPred { get; }
    bool is_OrPred { get; }
    DB._IDbKey dtor_key { get; }
    DB._ITable dtor_table { get; }
    DB._IDbPred dtor_pred { get; }
    DB._IDbPred dtor_left { get; }
    DB._IDbPred dtor_right { get; }
    _IDbPred DowncastClone();
  }
  public abstract class DbPred : _IDbPred {
    public DbPred() {
    }
    private static readonly DB._IDbPred theDefault = create_TruePred();
    public static DB._IDbPred Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbPred> _TYPE = new Dafny.TypeDescriptor<DB._IDbPred>(DB.DbPred.Default());
    public static Dafny.TypeDescriptor<DB._IDbPred> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbPred create_TruePred() {
      return new DbPred_TruePred();
    }
    public static _IDbPred create_FalsePred() {
      return new DbPred_FalsePred();
    }
    public static _IDbPred create_HasKeyPred(DB._IDbKey key) {
      return new DbPred_HasKeyPred(key);
    }
    public static _IDbPred create_TableHasAnyPred(DB._ITable table) {
      return new DbPred_TableHasAnyPred(table);
    }
    public static _IDbPred create_TableHasKeyPred(DB._ITable table, DB._IDbKey key) {
      return new DbPred_TableHasKeyPred(table, key);
    }
    public static _IDbPred create_NotPred(DB._IDbPred pred) {
      return new DbPred_NotPred(pred);
    }
    public static _IDbPred create_AndPred(DB._IDbPred left, DB._IDbPred right) {
      return new DbPred_AndPred(left, right);
    }
    public static _IDbPred create_OrPred(DB._IDbPred left, DB._IDbPred right) {
      return new DbPred_OrPred(left, right);
    }
    public bool is_TruePred { get { return this is DbPred_TruePred; } }
    public bool is_FalsePred { get { return this is DbPred_FalsePred; } }
    public bool is_HasKeyPred { get { return this is DbPred_HasKeyPred; } }
    public bool is_TableHasAnyPred { get { return this is DbPred_TableHasAnyPred; } }
    public bool is_TableHasKeyPred { get { return this is DbPred_TableHasKeyPred; } }
    public bool is_NotPred { get { return this is DbPred_NotPred; } }
    public bool is_AndPred { get { return this is DbPred_AndPred; } }
    public bool is_OrPred { get { return this is DbPred_OrPred; } }
    public DB._IDbKey dtor_key {
      get {
        var d = this;
        if (d is DbPred_HasKeyPred) { return ((DbPred_HasKeyPred)d)._key; }
        return ((DbPred_TableHasKeyPred)d)._key;
      }
    }
    public DB._ITable dtor_table {
      get {
        var d = this;
        if (d is DbPred_TableHasAnyPred) { return ((DbPred_TableHasAnyPred)d)._table; }
        return ((DbPred_TableHasKeyPred)d)._table;
      }
    }
    public DB._IDbPred dtor_pred {
      get {
        var d = this;
        return ((DbPred_NotPred)d)._pred;
      }
    }
    public DB._IDbPred dtor_left {
      get {
        var d = this;
        if (d is DbPred_AndPred) { return ((DbPred_AndPred)d)._left; }
        return ((DbPred_OrPred)d)._left;
      }
    }
    public DB._IDbPred dtor_right {
      get {
        var d = this;
        if (d is DbPred_AndPred) { return ((DbPred_AndPred)d)._right; }
        return ((DbPred_OrPred)d)._right;
      }
    }
    public abstract _IDbPred DowncastClone();
  }
  public class DbPred_TruePred : DbPred {
    public DbPred_TruePred() : base() {
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_TruePred();
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_TruePred;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.TruePred";
      return s;
    }
  }
  public class DbPred_FalsePred : DbPred {
    public DbPred_FalsePred() : base() {
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_FalsePred();
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_FalsePred;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.FalsePred";
      return s;
    }
  }
  public class DbPred_HasKeyPred : DbPred {
    public readonly DB._IDbKey _key;
    public DbPred_HasKeyPred(DB._IDbKey key) : base() {
      this._key = key;
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_HasKeyPred(_key);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_HasKeyPred;
      return oth != null && object.Equals(this._key, oth._key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.HasKeyPred";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ")";
      return s;
    }
  }
  public class DbPred_TableHasAnyPred : DbPred {
    public readonly DB._ITable _table;
    public DbPred_TableHasAnyPred(DB._ITable table) : base() {
      this._table = table;
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_TableHasAnyPred(_table);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_TableHasAnyPred;
      return oth != null && object.Equals(this._table, oth._table);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._table));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.TableHasAnyPred";
      s += "(";
      s += Dafny.Helpers.ToString(this._table);
      s += ")";
      return s;
    }
  }
  public class DbPred_TableHasKeyPred : DbPred {
    public readonly DB._ITable _table;
    public readonly DB._IDbKey _key;
    public DbPred_TableHasKeyPred(DB._ITable table, DB._IDbKey key) : base() {
      this._table = table;
      this._key = key;
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_TableHasKeyPred(_table, _key);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_TableHasKeyPred;
      return oth != null && object.Equals(this._table, oth._table) && object.Equals(this._key, oth._key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._table));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.TableHasKeyPred";
      s += "(";
      s += Dafny.Helpers.ToString(this._table);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key);
      s += ")";
      return s;
    }
  }
  public class DbPred_NotPred : DbPred {
    public readonly DB._IDbPred _pred;
    public DbPred_NotPred(DB._IDbPred pred) : base() {
      this._pred = pred;
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_NotPred(_pred);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_NotPred;
      return oth != null && object.Equals(this._pred, oth._pred);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pred));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.NotPred";
      s += "(";
      s += Dafny.Helpers.ToString(this._pred);
      s += ")";
      return s;
    }
  }
  public class DbPred_AndPred : DbPred {
    public readonly DB._IDbPred _left;
    public readonly DB._IDbPred _right;
    public DbPred_AndPred(DB._IDbPred left, DB._IDbPred right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_AndPred(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_AndPred;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.AndPred";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class DbPred_OrPred : DbPred {
    public readonly DB._IDbPred _left;
    public readonly DB._IDbPred _right;
    public DbPred_OrPred(DB._IDbPred left, DB._IDbPred right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IDbPred DowncastClone() {
      if (this is _IDbPred dt) { return dt; }
      return new DbPred_OrPred(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbPred_OrPred;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbPred.OrPred";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }

  public interface _IDbQuery {
    bool is_AllRows { get; }
    bool is_RowsInTable { get; }
    bool is_RowWithKey { get; }
    bool is_RowsMatching { get; }
    DB._ITable dtor_table { get; }
    DB._IDbKey dtor_key { get; }
    DB._IDbPred dtor_pred { get; }
    _IDbQuery DowncastClone();
  }
  public abstract class DbQuery : _IDbQuery {
    public DbQuery() {
    }
    private static readonly DB._IDbQuery theDefault = create_AllRows();
    public static DB._IDbQuery Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbQuery> _TYPE = new Dafny.TypeDescriptor<DB._IDbQuery>(DB.DbQuery.Default());
    public static Dafny.TypeDescriptor<DB._IDbQuery> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbQuery create_AllRows() {
      return new DbQuery_AllRows();
    }
    public static _IDbQuery create_RowsInTable(DB._ITable table) {
      return new DbQuery_RowsInTable(table);
    }
    public static _IDbQuery create_RowWithKey(DB._IDbKey key) {
      return new DbQuery_RowWithKey(key);
    }
    public static _IDbQuery create_RowsMatching(DB._IDbPred pred) {
      return new DbQuery_RowsMatching(pred);
    }
    public bool is_AllRows { get { return this is DbQuery_AllRows; } }
    public bool is_RowsInTable { get { return this is DbQuery_RowsInTable; } }
    public bool is_RowWithKey { get { return this is DbQuery_RowWithKey; } }
    public bool is_RowsMatching { get { return this is DbQuery_RowsMatching; } }
    public DB._ITable dtor_table {
      get {
        var d = this;
        return ((DbQuery_RowsInTable)d)._table;
      }
    }
    public DB._IDbKey dtor_key {
      get {
        var d = this;
        return ((DbQuery_RowWithKey)d)._key;
      }
    }
    public DB._IDbPred dtor_pred {
      get {
        var d = this;
        return ((DbQuery_RowsMatching)d)._pred;
      }
    }
    public abstract _IDbQuery DowncastClone();
  }
  public class DbQuery_AllRows : DbQuery {
    public DbQuery_AllRows() : base() {
    }
    public override _IDbQuery DowncastClone() {
      if (this is _IDbQuery dt) { return dt; }
      return new DbQuery_AllRows();
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbQuery_AllRows;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbQuery.AllRows";
      return s;
    }
  }
  public class DbQuery_RowsInTable : DbQuery {
    public readonly DB._ITable _table;
    public DbQuery_RowsInTable(DB._ITable table) : base() {
      this._table = table;
    }
    public override _IDbQuery DowncastClone() {
      if (this is _IDbQuery dt) { return dt; }
      return new DbQuery_RowsInTable(_table);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbQuery_RowsInTable;
      return oth != null && object.Equals(this._table, oth._table);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._table));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbQuery.RowsInTable";
      s += "(";
      s += Dafny.Helpers.ToString(this._table);
      s += ")";
      return s;
    }
  }
  public class DbQuery_RowWithKey : DbQuery {
    public readonly DB._IDbKey _key;
    public DbQuery_RowWithKey(DB._IDbKey key) : base() {
      this._key = key;
    }
    public override _IDbQuery DowncastClone() {
      if (this is _IDbQuery dt) { return dt; }
      return new DbQuery_RowWithKey(_key);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbQuery_RowWithKey;
      return oth != null && object.Equals(this._key, oth._key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbQuery.RowWithKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ")";
      return s;
    }
  }
  public class DbQuery_RowsMatching : DbQuery {
    public readonly DB._IDbPred _pred;
    public DbQuery_RowsMatching(DB._IDbPred pred) : base() {
      this._pred = pred;
    }
    public override _IDbQuery DowncastClone() {
      if (this is _IDbQuery dt) { return dt; }
      return new DbQuery_RowsMatching(_pred);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbQuery_RowsMatching;
      return oth != null && object.Equals(this._pred, oth._pred);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pred));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbQuery.RowsMatching";
      s += "(";
      s += Dafny.Helpers.ToString(this._pred);
      s += ")";
      return s;
    }
  }

  public interface _IDbProgram {
    bool is_Return { get; }
    bool is_Seq { get; }
    bool is_Lookup { get; }
    bool is_Exists { get; }
    bool is_Insert { get; }
    bool is_Update { get; }
    bool is_DeleteRow { get; }
    bool is_If { get; }
    bool is_ForEach { get; }
    DB._IDbProgram dtor_p1 { get; }
    DB._IDbProgram dtor_p2 { get; }
    DB._ITable dtor_table { get; }
    DB._IDbKey dtor_key { get; }
    DB._IDbPred dtor_pred { get; }
    DB._IDbValue dtor_row { get; }
    DB._IDbValue dtor_patch { get; }
    DB._IDbPred dtor_cond { get; }
    DB._IDbProgram dtor_thenP { get; }
    DB._IDbProgram dtor_elseP { get; }
    DB._IDbQuery dtor_query { get; }
    DB._IDbProgram dtor_body { get; }
    _IDbProgram DowncastClone();
  }
  public abstract class DbProgram : _IDbProgram {
    public DbProgram() {
    }
    private static readonly DB._IDbProgram theDefault = create_Return();
    public static DB._IDbProgram Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DB._IDbProgram> _TYPE = new Dafny.TypeDescriptor<DB._IDbProgram>(DB.DbProgram.Default());
    public static Dafny.TypeDescriptor<DB._IDbProgram> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDbProgram create_Return() {
      return new DbProgram_Return();
    }
    public static _IDbProgram create_Seq(DB._IDbProgram p1, DB._IDbProgram p2) {
      return new DbProgram_Seq(p1, p2);
    }
    public static _IDbProgram create_Lookup(DB._ITable table, DB._IDbKey key) {
      return new DbProgram_Lookup(table, key);
    }
    public static _IDbProgram create_Exists(DB._ITable table, DB._IDbPred pred) {
      return new DbProgram_Exists(table, pred);
    }
    public static _IDbProgram create_Insert(DB._IDbValue row) {
      return new DbProgram_Insert(row);
    }
    public static _IDbProgram create_Update(DB._IDbKey key, DB._IDbValue patch) {
      return new DbProgram_Update(key, patch);
    }
    public static _IDbProgram create_DeleteRow(DB._IDbKey key) {
      return new DbProgram_DeleteRow(key);
    }
    public static _IDbProgram create_If(DB._IDbPred cond, DB._IDbProgram thenP, DB._IDbProgram elseP) {
      return new DbProgram_If(cond, thenP, elseP);
    }
    public static _IDbProgram create_ForEach(DB._IDbQuery query, DB._IDbProgram body) {
      return new DbProgram_ForEach(query, body);
    }
    public bool is_Return { get { return this is DbProgram_Return; } }
    public bool is_Seq { get { return this is DbProgram_Seq; } }
    public bool is_Lookup { get { return this is DbProgram_Lookup; } }
    public bool is_Exists { get { return this is DbProgram_Exists; } }
    public bool is_Insert { get { return this is DbProgram_Insert; } }
    public bool is_Update { get { return this is DbProgram_Update; } }
    public bool is_DeleteRow { get { return this is DbProgram_DeleteRow; } }
    public bool is_If { get { return this is DbProgram_If; } }
    public bool is_ForEach { get { return this is DbProgram_ForEach; } }
    public DB._IDbProgram dtor_p1 {
      get {
        var d = this;
        return ((DbProgram_Seq)d)._p1;
      }
    }
    public DB._IDbProgram dtor_p2 {
      get {
        var d = this;
        return ((DbProgram_Seq)d)._p2;
      }
    }
    public DB._ITable dtor_table {
      get {
        var d = this;
        if (d is DbProgram_Lookup) { return ((DbProgram_Lookup)d)._table; }
        return ((DbProgram_Exists)d)._table;
      }
    }
    public DB._IDbKey dtor_key {
      get {
        var d = this;
        if (d is DbProgram_Lookup) { return ((DbProgram_Lookup)d)._key; }
        if (d is DbProgram_Update) { return ((DbProgram_Update)d)._key; }
        return ((DbProgram_DeleteRow)d)._key;
      }
    }
    public DB._IDbPred dtor_pred {
      get {
        var d = this;
        return ((DbProgram_Exists)d)._pred;
      }
    }
    public DB._IDbValue dtor_row {
      get {
        var d = this;
        return ((DbProgram_Insert)d)._row;
      }
    }
    public DB._IDbValue dtor_patch {
      get {
        var d = this;
        return ((DbProgram_Update)d)._patch;
      }
    }
    public DB._IDbPred dtor_cond {
      get {
        var d = this;
        return ((DbProgram_If)d)._cond;
      }
    }
    public DB._IDbProgram dtor_thenP {
      get {
        var d = this;
        return ((DbProgram_If)d)._thenP;
      }
    }
    public DB._IDbProgram dtor_elseP {
      get {
        var d = this;
        return ((DbProgram_If)d)._elseP;
      }
    }
    public DB._IDbQuery dtor_query {
      get {
        var d = this;
        return ((DbProgram_ForEach)d)._query;
      }
    }
    public DB._IDbProgram dtor_body {
      get {
        var d = this;
        return ((DbProgram_ForEach)d)._body;
      }
    }
    public abstract _IDbProgram DowncastClone();
  }
  public class DbProgram_Return : DbProgram {
    public DbProgram_Return() : base() {
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_Return();
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_Return;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.Return";
      return s;
    }
  }
  public class DbProgram_Seq : DbProgram {
    public readonly DB._IDbProgram _p1;
    public readonly DB._IDbProgram _p2;
    public DbProgram_Seq(DB._IDbProgram p1, DB._IDbProgram p2) : base() {
      this._p1 = p1;
      this._p2 = p2;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_Seq(_p1, _p2);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_Seq;
      return oth != null && object.Equals(this._p1, oth._p1) && object.Equals(this._p2, oth._p2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._p1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._p2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.Seq";
      s += "(";
      s += Dafny.Helpers.ToString(this._p1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._p2);
      s += ")";
      return s;
    }
  }
  public class DbProgram_Lookup : DbProgram {
    public readonly DB._ITable _table;
    public readonly DB._IDbKey _key;
    public DbProgram_Lookup(DB._ITable table, DB._IDbKey key) : base() {
      this._table = table;
      this._key = key;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_Lookup(_table, _key);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_Lookup;
      return oth != null && object.Equals(this._table, oth._table) && object.Equals(this._key, oth._key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._table));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.Lookup";
      s += "(";
      s += Dafny.Helpers.ToString(this._table);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key);
      s += ")";
      return s;
    }
  }
  public class DbProgram_Exists : DbProgram {
    public readonly DB._ITable _table;
    public readonly DB._IDbPred _pred;
    public DbProgram_Exists(DB._ITable table, DB._IDbPred pred) : base() {
      this._table = table;
      this._pred = pred;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_Exists(_table, _pred);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_Exists;
      return oth != null && object.Equals(this._table, oth._table) && object.Equals(this._pred, oth._pred);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._table));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pred));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.Exists";
      s += "(";
      s += Dafny.Helpers.ToString(this._table);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pred);
      s += ")";
      return s;
    }
  }
  public class DbProgram_Insert : DbProgram {
    public readonly DB._IDbValue _row;
    public DbProgram_Insert(DB._IDbValue row) : base() {
      this._row = row;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_Insert(_row);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_Insert;
      return oth != null && object.Equals(this._row, oth._row);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._row));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.Insert";
      s += "(";
      s += Dafny.Helpers.ToString(this._row);
      s += ")";
      return s;
    }
  }
  public class DbProgram_Update : DbProgram {
    public readonly DB._IDbKey _key;
    public readonly DB._IDbValue _patch;
    public DbProgram_Update(DB._IDbKey key, DB._IDbValue patch) : base() {
      this._key = key;
      this._patch = patch;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_Update(_key, _patch);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_Update;
      return oth != null && object.Equals(this._key, oth._key) && object.Equals(this._patch, oth._patch);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._patch));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.Update";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._patch);
      s += ")";
      return s;
    }
  }
  public class DbProgram_DeleteRow : DbProgram {
    public readonly DB._IDbKey _key;
    public DbProgram_DeleteRow(DB._IDbKey key) : base() {
      this._key = key;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_DeleteRow(_key);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_DeleteRow;
      return oth != null && object.Equals(this._key, oth._key);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.DeleteRow";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ")";
      return s;
    }
  }
  public class DbProgram_If : DbProgram {
    public readonly DB._IDbPred _cond;
    public readonly DB._IDbProgram _thenP;
    public readonly DB._IDbProgram _elseP;
    public DbProgram_If(DB._IDbPred cond, DB._IDbProgram thenP, DB._IDbProgram elseP) : base() {
      this._cond = cond;
      this._thenP = thenP;
      this._elseP = elseP;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_If(_cond, _thenP, _elseP);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_If;
      return oth != null && object.Equals(this._cond, oth._cond) && object.Equals(this._thenP, oth._thenP) && object.Equals(this._elseP, oth._elseP);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._thenP));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elseP));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.If";
      s += "(";
      s += Dafny.Helpers.ToString(this._cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._thenP);
      s += ", ";
      s += Dafny.Helpers.ToString(this._elseP);
      s += ")";
      return s;
    }
  }
  public class DbProgram_ForEach : DbProgram {
    public readonly DB._IDbQuery _query;
    public readonly DB._IDbProgram _body;
    public DbProgram_ForEach(DB._IDbQuery query, DB._IDbProgram body) : base() {
      this._query = query;
      this._body = body;
    }
    public override _IDbProgram DowncastClone() {
      if (this is _IDbProgram dt) { return dt; }
      return new DbProgram_ForEach(_query, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DB.DbProgram_ForEach;
      return oth != null && object.Equals(this._query, oth._query) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._query));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DB.DbProgram.ForEach";
      s += "(";
      s += Dafny.Helpers.ToString(this._query);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }

  public partial class Database {
    public Database() {
      this.operations = Dafny.Sequence<DB._IDbChange>.Empty;
    }
    public Dafny.ISequence<DB._IDbChange> operations {get; set;}
    public void __ctor()
    {
      (this).operations = Dafny.Sequence<DB._IDbChange>.FromElements();
    }
    public void ApplyOperations(Dafny.ISequence<DB._IDbChange> changes)
    {
      (this).operations = Dafny.Sequence<DB._IDbChange>.Concat(this.operations, changes);
    }
    public Dafny.ISequence<DB._IDbChange> GetOperations()
    {
      Dafny.ISequence<DB._IDbChange> ops = Dafny.Sequence<DB._IDbChange>.Empty;
      ops = this.operations;
      return ops;
    }
  }
} // end of namespace DB
namespace DuctTools {


  public interface _IUserInfo {
    bool is_UserInfo { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_email { get; }
    Dafny.ISequence<Dafny.Rune> dtor_picture { get; }
    bool dtor_authenticated { get; }
    _IUserInfo DowncastClone();
  }
  public class UserInfo : _IUserInfo {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _email;
    public readonly Dafny.ISequence<Dafny.Rune> _picture;
    public readonly bool _authenticated;
    public UserInfo(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> email, Dafny.ISequence<Dafny.Rune> picture, bool authenticated) {
      this._name = name;
      this._email = email;
      this._picture = picture;
      this._authenticated = authenticated;
    }
    public _IUserInfo DowncastClone() {
      if (this is _IUserInfo dt) { return dt; }
      return new UserInfo(_name, _email, _picture, _authenticated);
    }
    public override bool Equals(object other) {
      var oth = other as DuctTools.UserInfo;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._email, oth._email) && object.Equals(this._picture, oth._picture) && this._authenticated == oth._authenticated;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._email));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._picture));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._authenticated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DuctTools.UserInfo.UserInfo";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += this._email.ToVerbatimString(true);
      s += ", ";
      s += this._picture.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._authenticated);
      s += ")";
      return s;
    }
    private static readonly DuctTools._IUserInfo theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, false);
    public static DuctTools._IUserInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DuctTools._IUserInfo> _TYPE = new Dafny.TypeDescriptor<DuctTools._IUserInfo>(DuctTools.UserInfo.Default());
    public static Dafny.TypeDescriptor<DuctTools._IUserInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUserInfo create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> email, Dafny.ISequence<Dafny.Rune> picture, bool authenticated) {
      return new UserInfo(name, email, picture, authenticated);
    }
    public static _IUserInfo create_UserInfo(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> email, Dafny.ISequence<Dafny.Rune> picture, bool authenticated) {
      return create(name, email, picture, authenticated);
    }
    public bool is_UserInfo { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_email {
      get {
        return this._email;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_picture {
      get {
        return this._picture;
      }
    }
    public bool dtor_authenticated {
      get {
        return this._authenticated;
      }
    }
  }

  public interface _IReturnType {
    bool is_Content { get; }
    bool is_ChallengeGoogle { get; }
    bool is_Redirect { get; }
    Dafny.ISequence<Dafny.Rune> dtor_body { get; }
    Dafny.ISequence<Dafny.Rune> dtor_returnUrl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_url { get; }
    _IReturnType DowncastClone();
  }
  public abstract class ReturnType : _IReturnType {
    public ReturnType() {
    }
    private static readonly DuctTools._IReturnType theDefault = create_Content(Dafny.Sequence<Dafny.Rune>.Empty);
    public static DuctTools._IReturnType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DuctTools._IReturnType> _TYPE = new Dafny.TypeDescriptor<DuctTools._IReturnType>(DuctTools.ReturnType.Default());
    public static Dafny.TypeDescriptor<DuctTools._IReturnType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReturnType create_Content(Dafny.ISequence<Dafny.Rune> body) {
      return new ReturnType_Content(body);
    }
    public static _IReturnType create_ChallengeGoogle(Dafny.ISequence<Dafny.Rune> returnUrl) {
      return new ReturnType_ChallengeGoogle(returnUrl);
    }
    public static _IReturnType create_Redirect(Dafny.ISequence<Dafny.Rune> url) {
      return new ReturnType_Redirect(url);
    }
    public bool is_Content { get { return this is ReturnType_Content; } }
    public bool is_ChallengeGoogle { get { return this is ReturnType_ChallengeGoogle; } }
    public bool is_Redirect { get { return this is ReturnType_Redirect; } }
    public Dafny.ISequence<Dafny.Rune> dtor_body {
      get {
        var d = this;
        return ((ReturnType_Content)d)._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_returnUrl {
      get {
        var d = this;
        return ((ReturnType_ChallengeGoogle)d)._returnUrl;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_url {
      get {
        var d = this;
        return ((ReturnType_Redirect)d)._url;
      }
    }
    public abstract _IReturnType DowncastClone();
  }
  public class ReturnType_Content : ReturnType {
    public readonly Dafny.ISequence<Dafny.Rune> _body;
    public ReturnType_Content(Dafny.ISequence<Dafny.Rune> body) : base() {
      this._body = body;
    }
    public override _IReturnType DowncastClone() {
      if (this is _IReturnType dt) { return dt; }
      return new ReturnType_Content(_body);
    }
    public override bool Equals(object other) {
      var oth = other as DuctTools.ReturnType_Content;
      return oth != null && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DuctTools.ReturnType.Content";
      s += "(";
      s += this._body.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ReturnType_ChallengeGoogle : ReturnType {
    public readonly Dafny.ISequence<Dafny.Rune> _returnUrl;
    public ReturnType_ChallengeGoogle(Dafny.ISequence<Dafny.Rune> returnUrl) : base() {
      this._returnUrl = returnUrl;
    }
    public override _IReturnType DowncastClone() {
      if (this is _IReturnType dt) { return dt; }
      return new ReturnType_ChallengeGoogle(_returnUrl);
    }
    public override bool Equals(object other) {
      var oth = other as DuctTools.ReturnType_ChallengeGoogle;
      return oth != null && object.Equals(this._returnUrl, oth._returnUrl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._returnUrl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DuctTools.ReturnType.ChallengeGoogle";
      s += "(";
      s += this._returnUrl.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ReturnType_Redirect : ReturnType {
    public readonly Dafny.ISequence<Dafny.Rune> _url;
    public ReturnType_Redirect(Dafny.ISequence<Dafny.Rune> url) : base() {
      this._url = url;
    }
    public override _IReturnType DowncastClone() {
      if (this is _IReturnType dt) { return dt; }
      return new ReturnType_Redirect(_url);
    }
    public override bool Equals(object other) {
      var oth = other as DuctTools.ReturnType_Redirect;
      return oth != null && object.Equals(this._url, oth._url);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._url));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DuctTools.ReturnType.Redirect";
      s += "(";
      s += this._url.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface IGeneratorSpec {
    bool PreCondition(DuctTools._IUserInfo u);
  }
  public class _Companion_IGeneratorSpec {
  }

  public interface IGeneratorCore : DuctTools.IGeneratorSpec {
    DB._IDbProgram Program(DuctTools._IUserInfo u);
    DuctTools._IReturnType Response(DuctTools._IUserInfo u);
    void Generate(DuctTools._IUserInfo u, out DuctTools._IReturnType payload, out DB._IDbProgram prog);
  }
  public class _Companion_IGeneratorCore {
    public static void Generate(DuctTools.IGeneratorCore _this, DuctTools._IUserInfo u, out DuctTools._IReturnType payload, out DB._IDbProgram prog)
    {
      payload = DuctTools.ReturnType.Default();
      prog = DB.DbProgram.Default();
      payload = (_this).Response(u);
      prog = (_this).Program(u);
    }
  }

  public partial class ApiEndpoint {
    public ApiEndpoint() {
      this.apiUrl = Dafny.Sequence<Dafny.Rune>.Empty;
      this.returnType = DuctTools.ReturnType.Default();
      this.generator = default(DuctTools.IGeneratorCore);
    }
    public Dafny.ISequence<Dafny.Rune> apiUrl {get; set;}
    public DuctTools._IReturnType returnType {get; set;}
    public DuctTools.IGeneratorCore generator {get; set;}
    public void __ctor(Dafny.ISequence<Dafny.Rune> apiUrl, DuctTools._IReturnType rt, DuctTools.IGeneratorCore generator)
    {
      (this).apiUrl = apiUrl;
      (this).returnType = rt;
      (this).generator = generator;
    }
  }

  public partial class AllApiEndpoints {
    public AllApiEndpoints() {
      this.endpoints = Dafny.Sequence<DuctTools.ApiEndpoint>.Empty;
    }
    public Dafny.ISequence<DuctTools.ApiEndpoint> endpoints {get; set;}
    public void __ctor()
    {
      (this).endpoints = Dafny.Sequence<DuctTools.ApiEndpoint>.FromElements();
    }
    public void Add(DuctTools.ApiEndpoint ep)
    {
      (this).endpoints = Dafny.Sequence<DuctTools.ApiEndpoint>.Concat(this.endpoints, Dafny.Sequence<DuctTools.ApiEndpoint>.FromElements(ep));
    }
    public BigInteger Count()
    {
      BigInteger n = BigInteger.Zero;
      n = new BigInteger((this.endpoints).Count);
      return n;
    }
    public DuctTools.ApiEndpoint Get(BigInteger i)
    {
      DuctTools.ApiEndpoint ep = default(DuctTools.ApiEndpoint);
      ep = (this.endpoints).Select(i);
      return ep;
    }
  }
} // end of namespace DuctTools
namespace SpecsTools {

  public partial class __default {
    public static bool Contains(Dafny.ISequence<Dafny.Rune> haystack, Dafny.ISequence<Dafny.Rune> needle)
    {
      if ((new BigInteger((needle).Count)).Sign == 0) {
        return true;
      } else if ((new BigInteger((haystack).Count)) < (new BigInteger((needle).Count))) {
        return false;
      } else {
        return (((haystack).Subsequence(BigInteger.Zero, new BigInteger((needle).Count))).Equals(needle)) || (SpecsTools.__default.Contains((haystack).Drop(BigInteger.One), needle));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> Link(Dafny.ISequence<Dafny.Rune> linkLabel, Dafny.ISequence<Dafny.Rune> url)
    {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<a href=\""), url), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\">")), linkLabel), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</a>"));
    }
  }
} // end of namespace SpecsTools
namespace DuctSpecs {

  public partial class __default {
    public static bool LandingPagePre(DuctTools._IUserInfo ctx) {
      return ((((((((((((!((ctx).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) && (!(SpecsTools.__default.Contains((ctx).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Signed in"))))) && (!(SpecsTools.__default.Contains((ctx).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Anonymous"))))) && (!(SpecsTools.__default.Contains((ctx).dtor_name, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Log out"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/logout")))))) && (!(SpecsTools.__default.Contains((ctx).dtor_name, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sign in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/login")))))) && (!(SpecsTools.__default.Contains((ctx).dtor_email, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Signed in"))))) && (!(SpecsTools.__default.Contains((ctx).dtor_email, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Anonymous"))))) && (!(SpecsTools.__default.Contains((ctx).dtor_email, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Log out"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/logout")))))) && (!(SpecsTools.__default.Contains((ctx).dtor_email, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sign in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/login")))))) && (!(SpecsTools.__default.Contains((ctx).dtor_picture, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Signed in"))))) && (!(SpecsTools.__default.Contains((ctx).dtor_picture, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Anonymous"))))) && (!(SpecsTools.__default.Contains((ctx).dtor_picture, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Log out"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/logout")))))) && (!(SpecsTools.__default.Contains((ctx).dtor_picture, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sign in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/login")))));
    }
    public static bool LandingPagePayloadPost(DuctTools._IUserInfo ctx, DuctTools._IReturnType payload)
    {
      var _pat_let_tv0 = ctx;
      var _pat_let_tv1 = ctx;
      var _pat_let_tv2 = ctx;
      var _pat_let_tv3 = ctx;
      var _pat_let_tv4 = ctx;
      var _pat_let_tv5 = ctx;
      var _pat_let_tv6 = ctx;
      return ((payload).is_Content) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((payload).dtor_body, _pat_let0_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let0_0, _0_html => (((((!(_0_html).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) && (SpecsTools.__default.Contains(_0_html, (_pat_let_tv0).dtor_name))) && ((((_pat_let_tv1).dtor_email).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) || (SpecsTools.__default.Contains(_0_html, (_pat_let_tv2).dtor_email)))) && ((((_pat_let_tv3).dtor_picture).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) || (SpecsTools.__default.Contains(_0_html, (_pat_let_tv4).dtor_picture)))) && (((_pat_let_tv5).dtor_authenticated) == ((SpecsTools.__default.Contains(_0_html, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Signed in"))) && (SpecsTools.__default.Contains(_0_html, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Log out"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/logout"))))))) && ((!((_pat_let_tv6).dtor_authenticated)) == ((SpecsTools.__default.Contains(_0_html, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Anonymous"))) && (SpecsTools.__default.Contains(_0_html, SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sign in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/login")))))))));
    }
    public static bool LandingPagePost(DuctTools._IUserInfo ctx, Dafny.ISequence<DB._IDbValue> before, DuctTools._IReturnType payload, Dafny.ISequence<DB._IDbValue> after)
    {
      return (DuctSpecs.__default.LandingPagePayloadPost(ctx, payload)) && ((after).Equals(before));
    }
    public static bool LoginPost(DuctTools._IUserInfo ctx, Dafny.ISequence<DB._IDbValue> before, DuctTools._IReturnType payload, Dafny.ISequence<DB._IDbValue> after)
    {
      return (object.Equals(payload, DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/save_user")))) && ((after).Equals(before));
    }
    public static bool SecurePost(DuctTools._IUserInfo ctx, Dafny.ISequence<DB._IDbValue> before, DuctTools._IReturnType payload, Dafny.ISequence<DB._IDbValue> after)
    {
      return ((after).Equals(before)) && ((((ctx).dtor_authenticated) ? ((((payload).is_Content) && (SpecsTools.__default.Contains((payload).dtor_body, (ctx).dtor_name))) && (SpecsTools.__default.Contains((payload).dtor_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("You are authenticated")))) : (object.Equals(payload, DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/secure"))))));
    }
    public static Dafny.ISequence<DB._IDbChange> SaveUserOperations(DuctTools._IUserInfo ctx) {
      if (((ctx).dtor_authenticated) && (!((ctx).dtor_email).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
        return Dafny.Sequence<DB._IDbChange>.FromElements(DB.DbChange.create_Put(DB.DbValue.create_DbPersistedUser(DB.PersistedUser.create((ctx).dtor_email, (ctx).dtor_name, (ctx).dtor_picture))));
      } else {
        return Dafny.Sequence<DB._IDbChange>.FromElements();
      }
    }
    public static bool SaveUserPost(DuctTools._IUserInfo ctx, Dafny.ISequence<DB._IDbValue> before, DuctTools._IReturnType payload, Dafny.ISequence<DB._IDbValue> after)
    {
      if (((ctx).dtor_authenticated) && (!((ctx).dtor_email).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
        DB._IDbValue _0_row = DB.DbValue.create_DbPersistedUser(DB.PersistedUser.create((ctx).dtor_email, (ctx).dtor_name, (ctx).dtor_picture));
        return (object.Equals(payload, DuctTools.ReturnType.create_Redirect(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")))) && ((after).Equals(Dafny.Sequence<DB._IDbValue>.Concat(DB.__default.FilterEntries(before, DB.DbKey.create_PersistedUserKey((ctx).dtor_email)), Dafny.Sequence<DB._IDbValue>.FromElements(_0_row))));
      } else {
        return (object.Equals(payload, DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/save_user")))) && ((after).Equals(before));
      }
    }
  }

  public interface LandingPageSpec : DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
  }
  public class _Companion_LandingPageSpec {
    public static bool PreCondition(DuctSpecs.LandingPageSpec _this, DuctTools._IUserInfo u) {
      return DuctSpecs.__default.LandingPagePre(u);
    }
  }

  public interface LoginChallengePageSpec : DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
  }
  public class _Companion_LoginChallengePageSpec {
    public static bool PreCondition(DuctSpecs.LoginChallengePageSpec _this, DuctTools._IUserInfo u) {
      return true;
    }
  }

  public interface SaveUserPageSpec : DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
  }
  public class _Companion_SaveUserPageSpec {
    public static bool PreCondition(DuctSpecs.SaveUserPageSpec _this, DuctTools._IUserInfo u) {
      return true;
    }
  }

  public interface SecurePageSpec : DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
  }
  public class _Companion_SecurePageSpec {
    public static bool PreCondition(DuctSpecs.SecurePageSpec _this, DuctTools._IUserInfo u) {
      return true;
    }
  }
} // end of namespace DuctSpecs
namespace DuctLandingImpl {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> LandingPageStatus(DuctTools._IUserInfo ctx) {
      if ((ctx).dtor_authenticated) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Signed in");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Anonymous");
      }
    }
    public static Dafny.ISequence<Dafny.Rune> LandingPageAction(DuctTools._IUserInfo ctx) {
      if ((ctx).dtor_authenticated) {
        return SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Log out"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/logout"));
      } else {
        return SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sign in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/login"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> LandingPagePicturePanel(DuctTools._IUserInfo ctx) {
      if (((ctx).dtor_picture).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"avatar avatar-fallback\">F</div>");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"avatar\"><img src=\""), (ctx).dtor_picture), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\" alt=\"")), (ctx).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\" /></div>"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> LandingPageEmailPanel(DuctTools._IUserInfo ctx) {
      if (((ctx).dtor_email).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<span class=\"meta-value muted\">No email linked</span>");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<span class=\"meta-value\">"), (ctx).dtor_email), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</span>"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> LandingPagePictureMeta(DuctTools._IUserInfo ctx) {
      if (((ctx).dtor_picture).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<span class=\"meta-value muted\">No profile photo</span>");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<span class=\"meta-value\">Profile image connected</span>");
      }
    }
    public static Dafny.ISequence<Dafny.Rune> LandingPageHtml(DuctTools._IUserInfo ctx) {
      Dafny.ISequence<Dafny.Rune> _0_status = DuctLandingImpl.__default.LandingPageStatus(ctx);
      Dafny.ISequence<Dafny.Rune> _1_action = DuctLandingImpl.__default.LandingPageAction(ctx);
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<title>Formic</title>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<style>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":root{--bg:#f7f3ea;--ink:#171717;--muted:#63635f;--card:#fffdf8;--accent:#0f766e;--line:rgba(23,23,23,.12);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*{box-sizing:border-box;}body{margin:0;font-family:\"Avenir Next\",\"Segoe UI\",sans-serif;background:linear-gradient(180deg,#faf7f0,#ebe7dd);color:var(--ink);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".shell{min-height:100vh;display:grid;place-items:center;padding:32px 18px;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".panel{width:min(920px,100%);background:rgba(255,253,248,.92);border:1px solid var(--line);border-radius:20px;overflow:hidden;box-shadow:0 24px 70px rgba(23,23,23,.12);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".hero{display:grid;grid-template-columns:150px 1fr;gap:26px;padding:32px;border-bottom:1px solid var(--line);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".avatar{width:150px;height:150px;border-radius:18px;overflow:hidden;background:#e5e0d6;border:1px solid var(--line);display:grid;place-items:center;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".avatar img{width:100%;height:100%;object-fit:cover;display:block;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".avatar-fallback{font-size:52px;font-weight:800;color:var(--accent);letter-spacing:.08em;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".eyebrow{margin:0 0 10px;font-size:12px;letter-spacing:.18em;text-transform:uppercase;color:var(--accent);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".title{margin:0;font-size:42px;line-height:1;font-weight:800;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".status-badge{display:inline-flex;align-items:center;gap:10px;margin-top:16px;padding:9px 14px;border-radius:999px;background:#fff;border:1px solid var(--line);font-size:14px;font-weight:700;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".status-dot{width:10px;height:10px;border-radius:999px;background:var(--accent);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".lede{margin:18px 0 0;color:var(--muted);font-size:16px;line-height:1.6;max-width:42rem;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".content{display:grid;grid-template-columns:1.2fr .9fr;gap:20px;padding:28px 32px 32px;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".card{padding:22px;border-radius:14px;background:rgba(255,255,255,.7);border:1px solid var(--line);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".card-title{margin:0 0 16px;font-size:13px;letter-spacing:.16em;text-transform:uppercase;color:var(--muted);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".meta-grid{display:grid;gap:14px;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".meta-row{display:flex;justify-content:space-between;gap:18px;padding-bottom:12px;border-bottom:1px solid rgba(23,23,23,.08);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".meta-row:last-child{border-bottom:0;padding-bottom:0;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".meta-label{font-weight:700;color:var(--muted);}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".meta-value{text-align:right;font-weight:600;max-width:22rem;overflow-wrap:anywhere;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".muted{color:var(--muted);font-weight:500;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".actions{display:flex;flex-wrap:wrap;gap:12px;margin-top:22px;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".actions a{display:inline-flex;align-items:center;justify-content:center;padding:13px 18px;border-radius:999px;text-decoration:none;font-weight:800;background:var(--accent);color:#fff;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".aside-copy{margin:0;color:var(--muted);line-height:1.7;}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("@media (max-width:780px){.hero,.content{grid-template-columns:1fr;}.avatar{width:112px;height:112px;border-radius:14px;}.title{font-size:34px;}}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</style></head><body>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<main class=\"shell\"><section class=\"panel\">")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"hero\">")), DuctLandingImpl.__default.LandingPagePicturePanel(ctx)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<p class=\"eyebrow\">Formic Landing Page</p>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<h1 class=\"title\">")), (ctx).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</h1>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"status-badge\"><span class=\"status-dot\"></span>")), _0_status), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<p class=\"lede\">A generated profile surface for the formic demo.</p>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div></div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"content\">")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<section class=\"card\">")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<p class=\"card-title\">Profile</p>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"meta-grid\">")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"meta-row\"><span class=\"meta-label\">Name</span><span class=\"meta-value\">")), (ctx).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</span></div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"meta-row\"><span class=\"meta-label\">Email</span>")), DuctLandingImpl.__default.LandingPageEmailPanel(ctx)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"meta-row\"><span class=\"meta-label\">Picture</span>")), DuctLandingImpl.__default.LandingPagePictureMeta(ctx)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"meta-row\"><span class=\"meta-label\">Session</span><span class=\"meta-value\">")), _0_status), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</span></div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<div class=\"actions\">")), _1_action), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</section>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<aside class=\"card\">")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<p class=\"card-title\">Notes</p>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<p class=\"aside-copy\">This page is generated from Dafny and rendered through the ASP.NET host.</p>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</aside>")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</div></section></main></body></html>"));
    }
  }

  public partial class FormicLandingPage : DuctSpecs.LandingPageSpec, DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
    public FormicLandingPage() {
    }
    public void Generate(DuctTools._IUserInfo u, out DuctTools._IReturnType payload, out DB._IDbProgram prog)
    {
      DuctTools._IReturnType _out0;
      DB._IDbProgram _out1;
      DuctTools._Companion_IGeneratorCore.Generate(this, u, out _out0, out _out1);
      payload = _out0;
      prog = _out1;
    }
    public bool PreCondition(DuctTools._IUserInfo u) {
      return DuctSpecs._Companion_LandingPageSpec.PreCondition(this, u);
    }
    public void __ctor()
    {
    }
    public DuctTools._IReturnType Response(DuctTools._IUserInfo u) {
      return DuctTools.ReturnType.create_Content(DuctLandingImpl.__default.LandingPageHtml(u));
    }
    public DB._IDbProgram Program(DuctTools._IUserInfo u) {
      return DB.DbProgram.create_Return();
    }
  }
} // end of namespace DuctLandingImpl
namespace DuctLoginImpl {


  public partial class LoginChallengePage : DuctSpecs.LoginChallengePageSpec, DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
    public LoginChallengePage() {
    }
    public void Generate(DuctTools._IUserInfo u, out DuctTools._IReturnType payload, out DB._IDbProgram prog)
    {
      DuctTools._IReturnType _out2;
      DB._IDbProgram _out3;
      DuctTools._Companion_IGeneratorCore.Generate(this, u, out _out2, out _out3);
      payload = _out2;
      prog = _out3;
    }
    public bool PreCondition(DuctTools._IUserInfo u) {
      return DuctSpecs._Companion_LoginChallengePageSpec.PreCondition(this, u);
    }
    public void __ctor()
    {
    }
    public DuctTools._IReturnType Response(DuctTools._IUserInfo u) {
      return DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/save_user"));
    }
    public DB._IDbProgram Program(DuctTools._IUserInfo u) {
      return DB.DbProgram.create_Return();
    }
  }
} // end of namespace DuctLoginImpl
namespace DuctSaveUserImpl {


  public partial class SaveUserPage : DuctSpecs.SaveUserPageSpec, DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
    public SaveUserPage() {
    }
    public void Generate(DuctTools._IUserInfo u, out DuctTools._IReturnType payload, out DB._IDbProgram prog)
    {
      DuctTools._IReturnType _out4;
      DB._IDbProgram _out5;
      DuctTools._Companion_IGeneratorCore.Generate(this, u, out _out4, out _out5);
      payload = _out4;
      prog = _out5;
    }
    public bool PreCondition(DuctTools._IUserInfo u) {
      return DuctSpecs._Companion_SaveUserPageSpec.PreCondition(this, u);
    }
    public void __ctor()
    {
    }
    public DuctTools._IReturnType Response(DuctTools._IUserInfo u) {
      if (((u).dtor_authenticated) && (!((u).dtor_email).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
        return DuctTools.ReturnType.create_Redirect(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"));
      } else {
        return DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/save_user"));
      }
    }
    public DB._IDbProgram Program(DuctTools._IUserInfo u) {
      if (((u).dtor_authenticated) && (!((u).dtor_email).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
        return DB.DbProgram.create_Insert(DB.DbValue.create_DbPersistedUser(DB.PersistedUser.create((u).dtor_email, (u).dtor_name, (u).dtor_picture)));
      } else {
        return DB.DbProgram.create_Return();
      }
    }
  }
} // end of namespace DuctSaveUserImpl
namespace DuctSecureImpl {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> SecureHtml(DuctTools._IUserInfo ctx) {
      Dafny.ISequence<Dafny.Rune> _0_logout = SpecsTools.__default.Link(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Log out"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/logout"));
      Dafny.ISequence<Dafny.Rune> _1_authText = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("You are authenticated.");
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<title>Secure</title></head><body><h1>Hello, ")), (ctx).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!</h1><p>")), _1_authText), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</p><p>")), _0_logout), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</p></body></html>"));
    }
  }

  public partial class SecurePage : DuctSpecs.SecurePageSpec, DuctTools.IGeneratorCore, DuctTools.IGeneratorSpec {
    public SecurePage() {
    }
    public void Generate(DuctTools._IUserInfo u, out DuctTools._IReturnType payload, out DB._IDbProgram prog)
    {
      DuctTools._IReturnType _out6;
      DB._IDbProgram _out7;
      DuctTools._Companion_IGeneratorCore.Generate(this, u, out _out6, out _out7);
      payload = _out6;
      prog = _out7;
    }
    public bool PreCondition(DuctTools._IUserInfo u) {
      return DuctSpecs._Companion_SecurePageSpec.PreCondition(this, u);
    }
    public void __ctor()
    {
    }
    public DuctTools._IReturnType Response(DuctTools._IUserInfo u) {
      if ((u).dtor_authenticated) {
        return DuctTools.ReturnType.create_Content(DuctSecureImpl.__default.SecureHtml(u));
      } else {
        return DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/secure"));
      }
    }
    public DB._IDbProgram Program(DuctTools._IUserInfo u) {
      return DB.DbProgram.create_Return();
    }
  }
} // end of namespace DuctSecureImpl
namespace DuctApis {


  public partial class Views {
    public Views() {
    }
    public static void EndPointsInterface()
    {
    }
    public static DuctTools.AllApiEndpoints Endpoints()
    {
      DuctTools.AllApiEndpoints all = default(DuctTools.AllApiEndpoints);
      DuctTools.AllApiEndpoints _0_catalog;
      DuctTools.AllApiEndpoints _nw0 = new DuctTools.AllApiEndpoints();
      _nw0.__ctor();
      _0_catalog = _nw0;
      DuctLandingImpl.FormicLandingPage _1_formic__landing;
      DuctLandingImpl.FormicLandingPage _nw1 = new DuctLandingImpl.FormicLandingPage();
      _nw1.__ctor();
      _1_formic__landing = _nw1;
      DuctTools.ApiEndpoint _2_home;
      DuctTools.ApiEndpoint _nw2 = new DuctTools.ApiEndpoint();
      _nw2.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"), DuctTools.ReturnType.create_Content(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), _1_formic__landing);
      _2_home = _nw2;
      (_0_catalog).Add(_2_home);
      DuctLoginImpl.LoginChallengePage _3_login__page;
      DuctLoginImpl.LoginChallengePage _nw3 = new DuctLoginImpl.LoginChallengePage();
      _nw3.__ctor();
      _3_login__page = _nw3;
      DuctTools.ApiEndpoint _4_login;
      DuctTools.ApiEndpoint _nw4 = new DuctTools.ApiEndpoint();
      _nw4.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/login"), DuctTools.ReturnType.create_ChallengeGoogle(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/save_user")), _3_login__page);
      _4_login = _nw4;
      (_0_catalog).Add(_4_login);
      DuctSaveUserImpl.SaveUserPage _5_save__user__page;
      DuctSaveUserImpl.SaveUserPage _nw5 = new DuctSaveUserImpl.SaveUserPage();
      _nw5.__ctor();
      _5_save__user__page = _nw5;
      DuctTools.ApiEndpoint _6_save__user;
      DuctTools.ApiEndpoint _nw6 = new DuctTools.ApiEndpoint();
      _nw6.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/save_user"), DuctTools.ReturnType.create_Content(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), _5_save__user__page);
      _6_save__user = _nw6;
      (_0_catalog).Add(_6_save__user);
      DuctSecureImpl.SecurePage _7_secure__page;
      DuctSecureImpl.SecurePage _nw7 = new DuctSecureImpl.SecurePage();
      _nw7.__ctor();
      _7_secure__page = _nw7;
      DuctTools.ApiEndpoint _8_secure;
      DuctTools.ApiEndpoint _nw8 = new DuctTools.ApiEndpoint();
      _nw8.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/secure"), DuctTools.ReturnType.create_Content(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), _7_secure__page);
      _8_secure = _nw8;
      (_0_catalog).Add(_8_secure);
      all = _0_catalog;
      return all;
    }
  }
} // end of namespace DuctApis
namespace _module {

} // end of namespace _module
