# Duct Project Architecture

This project defines web API behavior in Dafny, verifies that endpoint
implementations satisfy their postconditions, translates the Dafny code into C#,
and hosts the generated logic with ASP.NET Core.

The key split is:

- Dafny source code defines specs, implementations, database programs, and API metadata.
- Generated C# mirrors the Dafny classes and datatypes.
- Hand-written C# hosts the generated logic as HTTP routes.

## End-To-End Box Diagram

Every important class, trait, or runtime component is shown as a box. Arrows
describe ownership, inheritance, calls, or translation boundaries.

```mermaid
flowchart LR
    subgraph DAFNY["Dafny source code (.dfy)"]
        direction TB

        DB["DB module<br/>DbValue, DbKey, DbProgram<br/>ExecuteProgram(before, program)"]
        USER["UserInfo datatype<br/>name, email, picture, authenticated"]
        RT["ReturnType datatype<br/>Content | ChallengeGoogle | Redirect"]
        GER["GeneratedEndpointResult datatype<br/>program: DbProgram<br/>response: ReturnType"]

        SPEC["IGeneratorSpec trait<br/>PreCondition(user)<br/>PostCondition(user, before, payload, after)"]
        CORE["IGeneratorCore trait<br/>Implementation(user)<br/>ImplementationCorrect(user)<br/>Generate(user)"]

        LANDSPEC["LandingPageSpec trait"]
        LOGINSPEC["LoginChallengePageSpec trait"]
        SAVESPEC["SaveUserPageSpec trait"]
        SECURESPEC["SecurePageSpec trait"]

        LANDIMPL["FormicLandingPage class<br/>Implementation(user)"]
        LOGINIMPL["LoginChallengePage class<br/>Implementation(user)"]
        SAVEIMPL["SaveUserPage class<br/>Implementation(user)<br/>ProveImplementationCorrect(user)"]
        SECUREIMPL["SecurePage class<br/>Implementation(user)"]

        PATH["apiUrl string<br/>route path metadata"]
        API["ApiEndpoint class<br/>apiUrl: string<br/>generator: IGeneratorCore"]
        CATALOG["AllApiEndpoints class<br/>endpoints: seq of ApiEndpoint<br/>Add | Count | Get"]
        VIEWS["Views class<br/>Endpoints()"]
    end

    TRANSLATOR["dafny translate cs<br/>translation step"]

    subgraph GENERATED["Generated C# code<br/>formic_site_duct/converted_duct/formic_duct.cs"]
        direction TB

        GDB["Generated DB types<br/>DbProgram, DbValue, ExecuteProgram helpers"]
        GCORE["Generated IGeneratorCore interface<br/>Implementation(user)<br/>Generate(user, out program, out payload)"]
        GIMPLS["Generated endpoint classes<br/>FormicLandingPage<br/>LoginChallengePage<br/>SaveUserPage<br/>SecurePage"]
        GAPI["Generated ApiEndpoint<br/>apiUrl + generator"]
        GVIEWS["Generated Views.Endpoints()<br/>builds endpoint catalog"]
    end

    subgraph HOST["Hand-written C# host<br/>formic_site_cs"]
        direction TB

        PROGRAM["DuctCore.cs / Program<br/>configures auth<br/>loads Views.Endpoints()"]
        MAPGET["ASP.NET MapGet handlers<br/>one route per ApiEndpoint.apiUrl"]
        CLAIMS["ClaimsPrincipal to UserInfo<br/>name, email, picture, authenticated"]
        RETURNRESP["ReturnResponse(generator, user, db)<br/>calls Generate<br/>executes DbProgram<br/>renders ReturnType"]
        DBBRIDGE["DuctDbBridge.cs<br/>executes generated DbProgram against storage"]
        HTTP["HTTP client response<br/>HTML content<br/>Google challenge<br/>redirect"]
    end

    SPEC -->|"is extended by"| CORE
    CORE -->|"requires implementation to return"| GER
    GER -->|"contains"| DB
    GER -->|"contains"| RT
    CORE -->|"reads"| USER
    CORE -->|"ImplementationCorrect checks PostCondition over ExecuteProgram"| SPEC
    SPEC -->|"PostCondition mentions before/after database state"| DB

    LANDSPEC -->|"extends"| CORE
    LOGINSPEC -->|"extends"| CORE
    SAVESPEC -->|"extends"| CORE
    SECURESPEC -->|"extends"| CORE

    LANDIMPL -->|"extends"| LANDSPEC
    LOGINIMPL -->|"extends"| LOGINSPEC
    SAVEIMPL -->|"extends"| SAVESPEC
    SECUREIMPL -->|"extends"| SECURESPEC

    SAVEIMPL -->|"proof establishes"| CORE

    API -->|"stores route string"| PATH
    API -->|"stores generator"| CORE
    CATALOG -->|"contains many"| API
    VIEWS -->|"creates catalog with endpoint boxes"| CATALOG
    VIEWS -->|"binds / to"| LANDIMPL
    VIEWS -->|"binds /login to"| LOGINIMPL
    VIEWS -->|"binds /save_user to"| SAVEIMPL
    VIEWS -->|"binds /secure to"| SECUREIMPL

    VIEWS -->|"included in translation input"| TRANSLATOR
    CORE -->|"included in translation input"| TRANSLATOR
    DB -->|"included in translation input"| TRANSLATOR
    TRANSLATOR -->|"emits generated C# boxes"| GVIEWS
    TRANSLATOR -->|"emits generated C# boxes"| GCORE
    TRANSLATOR -->|"emits generated C# boxes"| GDB
    DB -->|"translated into"| GDB
    CORE -->|"translated into"| GCORE
    LANDIMPL -->|"translated into"| GIMPLS
    LOGINIMPL -->|"translated into"| GIMPLS
    SAVEIMPL -->|"translated into"| GIMPLS
    SECUREIMPL -->|"translated into"| GIMPLS
    API -->|"translated into"| GAPI
    VIEWS -->|"translated into"| GVIEWS

    PROGRAM -->|"calls"| GVIEWS
    GVIEWS -->|"returns generated catalog of"| GAPI
    GAPI -->|"provides apiUrl to"| MAPGET
    GAPI -->|"provides generator to"| RETURNRESP
    MAPGET -->|"creates user from request"| CLAIMS
    CLAIMS -->|"passes generated UserInfo to"| RETURNRESP
    RETURNRESP -->|"calls generated Generate"| GCORE
    GCORE -->|"dispatches to generated Implementation"| GIMPLS
    GIMPLS -->|"returns generated DbProgram + ReturnType"| RETURNRESP
    RETURNRESP -->|"sends program to"| DBBRIDGE
    DBBRIDGE -->|"executes"| GDB
    RETURNRESP -->|"turns ReturnType into"| HTTP
```

## Dafny Spec And Implementation Relationship

This diagram focuses only on Dafny. The specs define the contract. The endpoint
classes implement the contract. `ImplementationCorrect` is the proof bridge.

```mermaid
flowchart TB
    SPECBOX["IGeneratorSpec<br/>PreCondition(user)<br/>PostCondition(user, before, payload, after)"]
    COREBOX["IGeneratorCore<br/>Implementation(user)<br/>ImplementationCorrect(user)<br/>Generate(user)"]
    RESULTBOX["GeneratedEndpointResult<br/>program: DbProgram<br/>response: ReturnType"]
    DBBOX["DbProgram + ExecuteProgram<br/>describes database effect"]
    RTBOX["ReturnType<br/>describes HTTP effect"]

    PAGE_SPEC["Endpoint spec trait<br/>LandingPageSpec / LoginChallengePageSpec<br/>SaveUserPageSpec / SecurePageSpec"]
    LLMBOX["LLM or developer implementation<br/>writes Implementation(user)"]
    IMPLBOX["Endpoint implementation class<br/>returns GeneratedEndpointResult"]
    PROOFBOX["Proof obligation<br/>ImplementationCorrect(user)"]
    GENBOX["Generate(user)<br/>unpacks Implementation(user)<br/>returns program + payload"]

    SPECBOX -->|"base proof contract"| COREBOX
    COREBOX -->|"Implementation must return"| RESULTBOX
    RESULTBOX -->|"program field"| DBBOX
    RESULTBOX -->|"response field"| RTBOX
    PAGE_SPEC -->|"extends"| COREBOX
    PAGE_SPEC -->|"specializes PostCondition"| SPECBOX
    LLMBOX -->|"authors"| IMPLBOX
    IMPLBOX -->|"extends endpoint spec trait"| PAGE_SPEC
    IMPLBOX -->|"must satisfy"| PROOFBOX
    PROOFBOX -->|"checks: PostCondition(user, before, response, ExecuteProgram(before, program))"| SPECBOX
    GENBOX -->|"calls only"| IMPLBOX
    GENBOX -->|"does not duplicate business logic"| RESULTBOX
```

## C# Runtime Relationship

This diagram focuses only on generated and hand-written C#.

```mermaid
flowchart TB
    subgraph GENCODE["Generated C# from Dafny"]
        GUSER["DuctTools.UserInfo"]
        GRET["DuctTools.ReturnType"]
        GPROG["DB.DbProgram"]
        GRESULT["DuctTools.GeneratedEndpointResult"]
        GCORE["DuctTools.IGeneratorCore"]
        GENDPOINTS["Generated endpoint classes<br/>Implementation(user)"]
        GAPI["DuctTools.ApiEndpoint<br/>apiUrl + generator"]
        GCATALOG["DuctTools.AllApiEndpoints"]
        GVIEWS["DuctApis.Views.Endpoints()"]
    end

    subgraph HOSTCODE["Hand-written ASP.NET C#"]
        APP["DuctCore.cs"]
        AUTH["ASP.NET authentication<br/>Google + cookie auth"]
        ROUTES["app.MapGet(path, handler)"]
        USERCONV["ToDafnyUserInfo(ClaimsPrincipal)"]
        RESP["ReturnResponse(generator, user, db)"]
        BRIDGE["DuctDbBridge.ExecuteProgram(db, program)"]
        OUT["IResult HTTP response"]
    end

    GRESULT -->|"contains"| GPROG
    GRESULT -->|"contains"| GRET
    GCORE -->|"implemented by"| GENDPOINTS
    GAPI -->|"holds"| GCORE
    GCATALOG -->|"contains"| GAPI
    GVIEWS -->|"creates"| GCATALOG

    APP -->|"configures"| AUTH
    APP -->|"calls generated"| GVIEWS
    APP -->|"iterates catalog"| GCATALOG
    GCATALOG -->|"returns each"| GAPI
    GAPI -->|"apiUrl becomes path"| ROUTES
    ROUTES -->|"request identity"| USERCONV
    USERCONV -->|"creates"| GUSER
    ROUTES -->|"passes generator + user"| RESP
    RESP -->|"calls Generate"| GCORE
    GCORE -->|"returns"| GPROG
    GCORE -->|"returns"| GRET
    RESP -->|"executes database program"| BRIDGE
    BRIDGE -->|"uses"| GPROG
    RESP -->|"maps ReturnType to ASP.NET result"| OUT
```

## Core Contracts

`IGeneratorSpec` defines what an endpoint must guarantee:

```dafny
PostCondition(
  u: UserInfo,
  before: seq<DbValue>,
  payload: ReturnType,
  after: seq<DbValue>)
```

`IGeneratorCore` requires the implementation function:

```dafny
function Implementation(u: UserInfo): GeneratedEndpointResult
```

`ImplementationCorrect` connects that implementation to the spec:

```dafny
forall before: seq<DbValue> ::
  PostCondition(
    u,
    before,
    Implementation(u).response,
    ExecuteProgram(before, Implementation(u).program))
```

`Generate` is intentionally thin. It evaluates the implementation once and
returns the two values needed by the host:

```dafny
method Generate(u: UserInfo) returns (prog: DbProgram, payload: ReturnType)
```

`ApiEndpoint` is only route metadata plus the generator:

```dafny
class ApiEndpoint {
  var apiUrl: string
  var generator: IGeneratorCore
}
```

The hand-written C# host owns HTTP concerns: authentication, route registration,
claim conversion, database bridge execution, and conversion from `ReturnType` to
an ASP.NET `IResult`.
