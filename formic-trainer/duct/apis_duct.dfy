module DuctApis {

    class Views {

        static method Endpoints() returns (all: AllApiEndpoints)
        {
            var catalog := new AllApiEndpoints();

            var trainer_loop := new ApiEndpoint("loop", new TrainerLoop());
            catalog.Add(trainer_loop);

            all := catalog; 
        }
    }
}