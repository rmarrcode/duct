module DuctLoginImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs

  class LoginChallengePage extends LoginChallengePageSpec {

    constructor () {}

    function Response(u: UserInfo): ReturnType
    {
      ChallengeGoogle("/save_user")
    }

    function Program(u: UserInfo): DbProgram
    {
      Return
    }
  }
}
