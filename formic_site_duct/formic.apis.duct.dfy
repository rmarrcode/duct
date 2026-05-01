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
            var home := new ApiEndpoint("/", ReturnType.Content(""), formic_landing);
            catalog.Add(home);

            var login_page := new LoginChallengePage();
            var login := new ApiEndpoint("/login", ReturnType.ChallengeGoogle("/save_user"), login_page);
            catalog.Add(login);

            var save_user_page := new SaveUserPage();
            var save_user := new ApiEndpoint("/save_user", ReturnType.Content(""), save_user_page);
            catalog.Add(save_user);

            var secure_page := new SecurePage();
            var secure := new ApiEndpoint("/secure", ReturnType.Content(""), secure_page);
            catalog.Add(secure);
            
            all := catalog; 
        }
    }
}
