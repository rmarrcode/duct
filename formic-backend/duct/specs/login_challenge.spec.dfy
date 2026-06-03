module LoginChallengeSpecs {

  import opened Tools
  import opened DB

  predicate LoginPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    payload == ReturnType.ChallengeGoogle("/save_user") &&
    after == before
  }

  trait {:termination false} LoginChallengePageSpec extends IGeneratorCore {

    predicate PreCondition(u: UserInfo)
    {
      true
    }

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>)
    {
      LoginPost(u, before, payload, after)
    }
  }
}
