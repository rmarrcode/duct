# Duct Project Architecture

This project defines web API behavior in Dafny, verifies that endpoint
implementations satisfy their postconditions, translates the Dafny code into C#,
and hosts the generated logic with ASP.NET Core.

The key split is:

- Dafny source code defines specs, implementations, database programs, and API metadata.
- Generated C# mirrors the Dafny classes and datatypes.
- Hand-written C# hosts the generated logic as HTTP routes.

## End-To-End Box Diagram

This diagram is intentionally boxy and large. It is organized as stacked lanes:
Dafny specification, Dafny implementation, Dafny API catalog, generated C#,
hand-written C# host, and one HTTP request.

```mermaid
%%{init: {
  "theme": "base",
  "themeVariables": {
    "fontFamily": "Arial, sans-serif",
    "fontSize": "34px",
    "background": "#ffffff",
    "mainBkg": "#ffffff",
    "primaryColor": "#ffffff",
    "secondaryColor": "#ffffff",
    "tertiaryColor": "#ffffff",
    "primaryTextColor": "#111827",
    "lineColor": "#111827",
    "clusterBkg": "#ffffff",
    "clusterBorder": "#111827",
    "edgeLabelBackground": "#ffffff"
  },
  "flowchart": {
    "htmlLabels": true,
    "nodeSpacing": 34,
    "rankSpacing": 56,
    "curve": "stepAfter",
    "padding": 12
  },
  "themeCSS": ".edgePath .path { stroke: #111827 !important; stroke-width: 7px !important; } .arrowheadPath { fill: #111827 !important; stroke: #111827 !important; } .edgeLabel { background-color: #ffffff !important; color: #111827 !important; } .node rect { rx: 0 !important; ry: 0 !important; }"
}}%%
flowchart TB
    subgraph SPEC_LANE["DAFNY SPECIFICATION LAYER"]
        direction LR
        USER["<b>UserInfo</b><br/>name<br/>email<br/>picture<br/>authenticated"]
        DB["<b>DB module</b><br/>DbValue<br/>DbKey<br/>DbProgram<br/>ExecuteProgram"]
        RT["<b>ReturnType</b><br/>Content<br/>ChallengeGoogle<br/>Redirect"]
        SPEC["<b>IGeneratorSpec</b><br/>PreCondition(user)<br/>PostCondition(user, before, payload, after)"]
        CORE["<b>IGeneratorCore</b><br/>Implementation(user)<br/>ImplementationCorrect(user)<br/>Generate(user)"]
        GER["<b>GeneratedEndpointResult</b><br/>program: DbProgram<br/>response: ReturnType"]
    end

    subgraph ENDPOINT_SPEC_LANE["DAFNY ENDPOINT SPEC TRAITS"]
        direction LR
        LANDSPEC["<b>LandingPageSpec</b><br/>landing page postcondition"]
        LOGINSPEC["<b>LoginChallengePageSpec</b><br/>login challenge postcondition"]
        SAVESPEC["<b>SaveUserPageSpec</b><br/>save-user postcondition"]
        SECURESPEC["<b>SecurePageSpec</b><br/>secure page postcondition"]
    end

    subgraph IMPL_LANE["DAFNY ENDPOINT IMPLEMENTATION CLASSES"]
        direction LR
        LANDIMPL["<b>FormicLandingPage</b><br/>Implementation(user)<br/>returns HTML content"]
        LOGINIMPL["<b>LoginChallengePage</b><br/>Implementation(user)<br/>returns Google challenge"]
        SAVEIMPL["<b>SaveUserPage</b><br/>Implementation(user)<br/>ProveImplementationCorrect(user)"]
        SECUREIMPL["<b>SecurePage</b><br/>Implementation(user)<br/>content or challenge"]
    end

    subgraph API_LANE["DAFNY API CATALOG"]
        direction LR
        API["<b>ApiEndpoint</b><br/>apiUrl: string<br/>generator: IGeneratorCore"]
        CATALOG["<b>AllApiEndpoints</b><br/>endpoints: seq of ApiEndpoint<br/>Add<br/>Count<br/>Get"]
        VIEWS["<b>Views.Endpoints()</b><br/>creates /<br/>creates /login<br/>creates /save_user<br/>creates /secure"]
    end

    TRANSLATOR["<b>dafny translate cs</b><br/>compiles Dafny source<br/>into generated C#"]

    subgraph GEN_LANE["GENERATED C#"]
        direction LR
        GCORE["<b>Generated IGeneratorCore</b><br/>Generate(user, out program, out payload)"]
        GIMPLS["<b>Generated endpoint classes</b><br/>FormicLandingPage<br/>LoginChallengePage<br/>SaveUserPage<br/>SecurePage"]
        GAPI["<b>Generated ApiEndpoint</b><br/>apiUrl<br/>generator"]
        GVIEWS["<b>Generated Views.Endpoints()</b><br/>returns generated endpoint catalog"]
        GDB["<b>Generated DB types</b><br/>DbProgram<br/>DbValue"]
    end

    subgraph HOST_LANE["HAND-WRITTEN C# HOST"]
        direction LR
        PROGRAM["<b>DuctCore.cs</b><br/>configures Google auth<br/>loads Views.Endpoints()"]
        MAPGET["<b>app.MapGet</b><br/>one route per apiUrl"]
        CLAIMS["<b>ToDafnyUserInfo</b><br/>ClaimsPrincipal to UserInfo"]
        RETURNRESP["<b>ReturnResponse</b><br/>calls Generate<br/>executes DbProgram<br/>renders ReturnType"]
        DBBRIDGE["<b>DuctDbBridge</b><br/>runs DbProgram against storage"]
        HTTP["<b>HTTP response</b><br/>HTML<br/>Google challenge<br/>redirect"]
    end

    SPEC -->|"extends"| CORE
    CORE -->|"returns"| GER
    GER -->|"program field"| DB
    GER -->|"response field"| RT
    CORE -->|"input"| USER

    CORE -->|"base trait"| LANDSPEC
    CORE -->|"base trait"| LOGINSPEC
    CORE -->|"base trait"| SAVESPEC
    CORE -->|"base trait"| SECURESPEC

    LANDSPEC -->|"extended by"| LANDIMPL
    LOGINSPEC -->|"extended by"| LOGINIMPL
    SAVESPEC -->|"extended by"| SAVEIMPL
    SECURESPEC -->|"extended by"| SECUREIMPL
    SAVEIMPL -->|"proves"| CORE

    API -->|"stores generator"| CORE
    VIEWS -->|"creates many"| API
    CATALOG -->|"contains"| API
    VIEWS -->|"returns"| CATALOG
    VIEWS -->|"binds routes to"| LANDIMPL
    VIEWS -->|"binds routes to"| LOGINIMPL
    VIEWS -->|"binds routes to"| SAVEIMPL
    VIEWS -->|"binds routes to"| SECUREIMPL

    DB --> TRANSLATOR
    CORE --> TRANSLATOR
    VIEWS --> TRANSLATOR
    LANDIMPL --> TRANSLATOR
    LOGINIMPL --> TRANSLATOR
    SAVEIMPL --> TRANSLATOR
    SECUREIMPL --> TRANSLATOR

    TRANSLATOR --> GDB
    TRANSLATOR --> GCORE
    TRANSLATOR --> GIMPLS
    TRANSLATOR --> GAPI
    TRANSLATOR --> GVIEWS

    PROGRAM -->|"calls"| GVIEWS
    GVIEWS -->|"catalog of"| GAPI
    GAPI -->|"path"| MAPGET
    GAPI -->|"generator"| RETURNRESP
    MAPGET -->|"request user"| CLAIMS
    CLAIMS -->|"UserInfo"| RETURNRESP
    RETURNRESP -->|"Generate"| GCORE
    GCORE -->|"Implementation"| GIMPLS
    GIMPLS -->|"DbProgram + ReturnType"| RETURNRESP
    RETURNRESP -->|"DbProgram"| DBBRIDGE
    DBBRIDGE -->|"uses generated DB"| GDB
    RETURNRESP -->|"ReturnType"| HTTP

    classDef dafny fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:34px;
    classDef impl fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:34px;
    classDef api fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:34px;
    classDef generated fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:34px;
    classDef host fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:34px;
    classDef bridge fill:#ffffff,stroke:#111827,stroke-width:8px,color:#111827,font-size:36px;

    class USER,DB,RT,SPEC,CORE,GER,LANDSPEC,LOGINSPEC,SAVESPEC,SECURESPEC dafny;
    class LANDIMPL,LOGINIMPL,SAVEIMPL,SECUREIMPL impl;
    class API,CATALOG,VIEWS api;
    class GCORE,GIMPLS,GAPI,GVIEWS,GDB generated;
    class PROGRAM,MAPGET,CLAIMS,RETURNRESP,DBBRIDGE,HTTP host;
    class TRANSLATOR bridge;
```

## Dafny Spec And Implementation Relationship

This diagram focuses only on Dafny. The specs define the contract. The endpoint
classes implement the contract. `ImplementationCorrect` is the proof bridge.

```mermaid
%%{init: {
  "theme": "base",
  "themeVariables": {
    "fontFamily": "Arial, sans-serif",
    "fontSize": "32px",
    "background": "#ffffff",
    "mainBkg": "#ffffff",
    "primaryColor": "#ffffff",
    "secondaryColor": "#ffffff",
    "tertiaryColor": "#ffffff",
    "primaryTextColor": "#111827",
    "lineColor": "#111827",
    "clusterBkg": "#ffffff",
    "clusterBorder": "#111827",
    "edgeLabelBackground": "#ffffff"
  },
  "flowchart": {
    "htmlLabels": true,
    "nodeSpacing": 32,
    "rankSpacing": 52,
    "curve": "stepAfter",
    "padding": 12
  },
  "themeCSS": ".edgePath .path { stroke: #111827 !important; stroke-width: 7px !important; } .arrowheadPath { fill: #111827 !important; stroke: #111827 !important; } .edgeLabel { background-color: #ffffff !important; color: #111827 !important; } .node rect { rx: 0 !important; ry: 0 !important; }"
}}%%
flowchart TB
    subgraph CONTRACT["DAFNY CONTRACT BOXES"]
        direction LR
        SPECBOX["<b>IGeneratorSpec</b><br/>PreCondition(user)<br/>PostCondition(user, before, payload, after)"]
        COREBOX["<b>IGeneratorCore</b><br/>Implementation(user)<br/>ImplementationCorrect(user)<br/>Generate(user)"]
        RESULTBOX["<b>GeneratedEndpointResult</b><br/>program: DbProgram<br/>response: ReturnType"]
    end

    subgraph EFFECTS["EFFECT BOXES"]
        direction LR
        DBBOX["<b>DbProgram + ExecuteProgram</b><br/>describes database effect"]
        RTBOX["<b>ReturnType</b><br/>describes HTTP effect"]
    end

    subgraph IMPLEMENTATION["IMPLEMENTATION BOXES"]
        direction LR
        PAGE_SPEC["<b>Endpoint spec trait</b><br/>LandingPageSpec<br/>LoginChallengePageSpec<br/>SaveUserPageSpec<br/>SecurePageSpec"]
        LLMBOX["<b>LLM or developer</b><br/>writes Implementation(user)"]
        IMPLBOX["<b>Endpoint implementation class</b><br/>returns GeneratedEndpointResult"]
        PROOFBOX["<b>Proof obligation</b><br/>ImplementationCorrect(user)"]
        GENBOX["<b>Generate(user)</b><br/>unpacks Implementation(user)<br/>returns program + payload"]
    end

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

    classDef box fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:32px;
    classDef effect fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:32px;
    classDef proof fill:#ffffff,stroke:#111827,stroke-width:8px,color:#111827,font-size:34px;

    class SPECBOX,COREBOX,RESULTBOX,PAGE_SPEC,LLMBOX,IMPLBOX,GENBOX box;
    class DBBOX,RTBOX effect;
    class PROOFBOX proof;
```

## C# Runtime Relationship

This diagram focuses only on generated and hand-written C#.

```mermaid
%%{init: {
  "theme": "base",
  "themeVariables": {
    "fontFamily": "Arial, sans-serif",
    "fontSize": "32px",
    "background": "#ffffff",
    "mainBkg": "#ffffff",
    "primaryColor": "#ffffff",
    "secondaryColor": "#ffffff",
    "tertiaryColor": "#ffffff",
    "primaryTextColor": "#111827",
    "lineColor": "#111827",
    "clusterBkg": "#ffffff",
    "clusterBorder": "#111827",
    "edgeLabelBackground": "#ffffff"
  },
  "flowchart": {
    "htmlLabels": true,
    "nodeSpacing": 32,
    "rankSpacing": 52,
    "curve": "stepAfter",
    "padding": 12
  },
  "themeCSS": ".edgePath .path { stroke: #111827 !important; stroke-width: 7px !important; } .arrowheadPath { fill: #111827 !important; stroke: #111827 !important; } .edgeLabel { background-color: #ffffff !important; color: #111827 !important; } .node rect { rx: 0 !important; ry: 0 !important; }"
}}%%
flowchart TB
    subgraph GENCODE["Generated C# from Dafny"]
        direction LR
        GUSER["<b>DuctTools.UserInfo</b>"]
        GRET["<b>DuctTools.ReturnType</b>"]
        GPROG["<b>DB.DbProgram</b>"]
        GRESULT["<b>DuctTools.GeneratedEndpointResult</b>"]
        GCORE["<b>DuctTools.IGeneratorCore</b>"]
        GENDPOINTS["<b>Generated endpoint classes</b><br/>Implementation(user)"]
        GAPI["<b>DuctTools.ApiEndpoint</b><br/>apiUrl<br/>generator"]
        GCATALOG["<b>DuctTools.AllApiEndpoints</b>"]
        GVIEWS["<b>DuctApis.Views.Endpoints()</b>"]
    end

    subgraph HOSTCODE["Hand-written ASP.NET C#"]
        direction LR
        APP["<b>DuctCore.cs</b>"]
        AUTH["<b>ASP.NET authentication</b><br/>Google + cookie auth"]
        ROUTES["<b>app.MapGet(path, handler)</b>"]
        USERCONV["<b>ToDafnyUserInfo</b><br/>ClaimsPrincipal to UserInfo"]
        RESP["<b>ReturnResponse</b><br/>generator, user, db"]
        BRIDGE["<b>DuctDbBridge.ExecuteProgram</b><br/>db, program"]
        OUT["<b>IResult HTTP response</b>"]
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

    classDef gen fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:32px;
    classDef host fill:#ffffff,stroke:#111827,stroke-width:7px,color:#111827,font-size:32px;

    class GUSER,GRET,GPROG,GRESULT,GCORE,GENDPOINTS,GAPI,GCATALOG,GVIEWS gen;
    class APP,AUTH,ROUTES,USERCONV,RESP,BRIDGE,OUT host;
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
