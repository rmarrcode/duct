module DuctApis {

    import opened Tools
    import opened LandingImpl
    import opened LoginImpl
    import opened SaveUserImpl
    import opened SecureImpl
    import opened UserInfoImpl

    class Views {

        static method Endpoints() returns (all: AllApiEndpoints)
        {
            var catalog := new AllApiEndpoints();

            var formic_landing := new FormicLandingPage();
            var home := new ApiEndpoint("/", formic_landing);
            catalog.Add(home);

            var login_page := new LoginChallengePage();
            // The URL here is no longer used by the host, so we can simplify it.
            var login := new ApiEndpoint("/login", login_page);
            catalog.Add(login);

            var save_user_page := new SaveUserPage();
            var save_user := new ApiEndpoint("/save_user", save_user_page);
            catalog.Add(save_user);

            var secure_page := new SecurePage();
            var secure := new ApiEndpoint("/secure", secure_page);
            catalog.Add(secure);
            
            var user_info_page := new UserInfoPage();
            var user_info := new ApiEndpoint("/user_info", user_info_page);
            catalog.Add(user_info);

            //var training_instructions_page := new TrainingInstructions();
            //var training_instructions := new ApiEndpoint("/training_instructions", training_instructions_page);
            //catalog.Add(training_instructions);

            all := catalog; 
        }
    }
}
