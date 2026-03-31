module DuctApis {

    import opened DuctImpl
    import opened DuctTools

    class Views {
        static method Endpoints() returns (all: AllApiEndpoints)
            ensures |all.endpoints| == 1
        {
            var catalog := new AllApiEndpoints();

            var formic_landing := new FormicLandingPage();
            var ep := new ApiEndpoint("/", ReturnType.Content, formic_landing);
            catalog.Add(ep);

            all := catalog;
        }
    }

}
