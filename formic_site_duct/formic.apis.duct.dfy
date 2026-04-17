module DuctApis {

    import opened DB
    import opened DuctImpl
    import opened DuctTools

    class Views {

        static method Endpoints() returns (all: AllApiEndpoints)
        {
            var catalog := new AllApiEndpoints();
            var appDb := new Database();

            var formic_landing := new FormicLandingPage();
            formic_landing.SetDb(appDb);
            var home := new ApiEndpoint("/", ReturnType.Content(""), formic_landing);
            catalog.Add(home);

            var login_page := new LoginChallengePage();
            login_page.SetDb(appDb);
            var login := new ApiEndpoint("/login", ReturnType.ChallengeGoogle("/"), login_page);
            catalog.Add(login);

            var save_user_page := new SaveUserPage();
            save_user_page.SetDb(appDb);
            var save_user := new ApiEndpoint("/save_user", ReturnType.Content(""), save_user_page);
            catalog.Add(save_user);

            var secure_page := new SecurePage();
            secure_page.SetDb(appDb);
            var secure := new ApiEndpoint("/secure", ReturnType.Content(""), secure_page);
            catalog.Add(secure);
            
            all := catalog;
        }
    }
}
