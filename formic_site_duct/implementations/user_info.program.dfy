module DuctSaveUserImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs

  class UserInfoPage extends UserInfoSpec {

    constructor () {}

    function Implementation(u: UserInfo): GeneratedEndpointResult
    {
        
    }

    lemma ProveImplementationCorrect(u: UserInfo)
      requires PreCondition(u)
      ensures ImplementationCorrect(u)
    {
    }
  }
}
