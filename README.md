# Duct Project Architecture

Duct is a backend framework that enables the development of web funtionality via formal specifications.
The philosophy behind this project is that specifications are an abstraction layers for LLM generated code.
I want to leverage the generative capabilities of LLMS as well as the power that comes with abstract formalizations.

A programmer defines web API behavior in Dafny; an LLM verifies that endpoint
implementations satisfy the dafny specifications, translates the Dafny code into C# to be run with 
ASP.NET Core.

## Diagrams

### End-To-End Architecture

```mermaid
flowchart TB
    subgraph DAFNY["DAFNY SOURCE"]
        SPEC["IGeneratorSpec<br/>PreCondition<br/>PostCondition"]
        CORE["IGeneratorCore<br/>Implementation<br/>ImplementationCorrect<br/>Generate"]
        TYPES["Core datatypes<br/>UserInfo<br/>DbProgram<br/>ReturnType<br/>GeneratedEndpointResult"]
        PAGE_SPECS["Endpoint spec traits<br/>LandingPageSpec<br/>LoginChallengePageSpec<br/>SaveUserPageSpec<br/>SecurePageSpec"]
        PAGE_IMPLS["Endpoint implementation classes<br/>FormicLandingPage<br/>LoginChallengePage<br/>SaveUserPage<br/>SecurePage"]
        VIEWS["Views.Endpoints<br/>builds the API catalog"]
        API["ApiEndpoint<br/>apiUrl<br/>generator"]
        CATALOG["AllApiEndpoints<br/>sequence of ApiEndpoint"]
    end

    TRANSLATE["dafny translate cs"]

    subgraph GENERATED["GENERATED C#"]
        GCORE["Generated IGeneratorCore"]
        GIMPLS["Generated endpoint classes"]
        GAPI["Generated ApiEndpoint"]
        GVIEWS["Generated Views.Endpoints"]
        GDB["Generated DB and ReturnType classes"]
    end

    subgraph HOST["HAND-WRITTEN C# HOST"]
        APP["DuctCore.cs<br/>configures auth<br/>loads endpoint catalog"]
        ROUTES["ASP.NET MapGet<br/>one handler per apiUrl"]
        USERINFO["ToDafnyUserInfo<br/>ClaimsPrincipal to UserInfo"]
        RESPONSE["ReturnResponse<br/>calls Generate<br/>executes DbProgram<br/>renders ReturnType"]
        DBBRIDGE["DuctDbBridge<br/>runs DbProgram against storage"]
        HTTP["HTTP response<br/>HTML<br/>Google challenge<br/>Redirect"]
    end

    SPEC --> CORE
    TYPES --> CORE
    CORE --> PAGE_SPECS
    PAGE_SPECS --> PAGE_IMPLS
    PAGE_IMPLS --> VIEWS
    CORE --> API
    API --> CATALOG
    VIEWS --> CATALOG

    DAFNY --> TRANSLATE
    TRANSLATE --> GENERATED

    GENERATED --> APP
    APP --> GVIEWS
    GVIEWS --> GAPI
    GAPI --> ROUTES
    ROUTES --> USERINFO
    USERINFO --> RESPONSE
    RESPONSE --> GCORE
    GCORE --> GIMPLS
    GIMPLS --> RESPONSE
    RESPONSE --> DBBRIDGE
    DBBRIDGE --> GDB
    RESPONSE --> HTTP

    classDef box fill:#ffffff,stroke:#111111,stroke-width:3px,color:#111111,font-size:18px;
    class SPEC,CORE,TYPES,PAGE_SPECS,PAGE_IMPLS,VIEWS,API,CATALOG,TRANSLATE,GCORE,GIMPLS,GAPI,GVIEWS,GDB,APP,ROUTES,USERINFO,RESPONSE,DBBRIDGE,HTTP box;
```

### Dafny Proof Contract

```mermaid
flowchart TB
    USER["UserInfo<br/>request context"]
    BEFORE["before<br/>sequence of DbValue"]
    SPEC["IGeneratorSpec<br/>PostCondition(user, before, payload, after)"]
    CORE["IGeneratorCore<br/>requires Implementation(user)"]
    LLM["LLM or developer<br/>writes endpoint Implementation"]
    RESULT["GeneratedEndpointResult<br/>program: DbProgram<br/>response: ReturnType"]
    EXECUTE["ExecuteProgram(before, program)"]
    AFTER["after<br/>database state after program"]
    PROOF["ImplementationCorrect(user)<br/>proves PostCondition for every before state"]
    GENERATE["Generate(user)<br/>calls Implementation once<br/>returns program and payload"]

    USER --> CORE
    CORE --> LLM
    LLM --> RESULT
    RESULT --> EXECUTE
    BEFORE --> EXECUTE
    EXECUTE --> AFTER
    RESULT --> PROOF
    AFTER --> PROOF
    SPEC --> PROOF
    RESULT --> GENERATE

    classDef box fill:#ffffff,stroke:#111111,stroke-width:3px,color:#111111,font-size:18px;
    class USER,BEFORE,SPEC,CORE,LLM,RESULT,EXECUTE,AFTER,PROOF,GENERATE box;
```

### Runtime Request Flow

```mermaid
flowchart LR
    CLIENT["Browser or API client"]
    ASPNET["ASP.NET Core<br/>MapGet route"]
    AUTH["Authentication middleware<br/>Google cookie identity"]
    USERINFO["ToDafnyUserInfo<br/>ClaimsPrincipal to UserInfo"]
    ENDPOINT["ApiEndpoint.generator<br/>generated IGeneratorCore"]
    GENERATE["Generate(user)<br/>returns DbProgram and ReturnType"]
    PROGRAM["DbProgram"]
    PAYLOAD["ReturnType"]
    DBBRIDGE["DuctDbBridge<br/>executes DbProgram"]
    RENDER["ReturnResponse<br/>maps ReturnType to IResult"]
    RESPONSE["HTTP response"]

    CLIENT --> ASPNET
    ASPNET --> AUTH
    AUTH --> USERINFO
    ASPNET --> ENDPOINT
    USERINFO --> GENERATE
    ENDPOINT --> GENERATE
    GENERATE --> PROGRAM
    GENERATE --> PAYLOAD
    PROGRAM --> DBBRIDGE
    PAYLOAD --> RENDER
    DBBRIDGE --> RENDER
    RENDER --> RESPONSE

    classDef box fill:#ffffff,stroke:#111111,stroke-width:3px,color:#111111,font-size:18px;
    class CLIENT,ASPNET,AUTH,USERINFO,ENDPOINT,GENERATE,PROGRAM,PAYLOAD,DBBRIDGE,RENDER,RESPONSE box;
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