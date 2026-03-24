import opened DuctImpl
import opened DuctApi

class Views {
    static method Endpoints() returns (all: AllApiEndpoints)
        ensures |all.endpoints| == 1
    {
        var catalog := new AllApiEndpoints();
        var generator := new FormicLandingPage();
        var ep := new ApiEndpoint("/", ReturnType.Content, generator);
        catalog.Add(ep);
        return catalog;
    }
}