module DuctApis {

    import opened DuctImpl
    import opened DuctTools

    class Views {
        static method Endpoints() returns (all: AllApiEndpoints)
        {
            var catalog := new AllApiEndpoints();

            var formic_landing := new FormicLandingPage();
            var home := new ApiEndpoint("/", ReturnType.Content(""), formic_landing);
            catalog.Add(home);

            var login_page := new LoginChallengePage();
            var login := new ApiEndpoint("/login", ReturnType.ChallengeGoogle("/"), login_page);
            catalog.Add(login);

            var secure_page := new SecurePage();
            var secure := new ApiEndpoint("/secure", ReturnType.Content(""), secure_page);
            catalog.Add(secure);
            
            all := catalog;
        }
    }
}
