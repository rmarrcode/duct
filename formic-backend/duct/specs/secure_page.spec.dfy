module SecurePageSpecs {

  import opened Tools
  import opened SpecsTools
  import opened DB

  predicate SecurePost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    after == before &&
    if ctx.authenticated then
      payload.Content? &&
      Contains(payload.body, ctx.name) &&
      Contains(payload.body, "You are authenticated")
    else
      payload == ReturnType.ChallengeGoogle("/secure")
  }

  trait {:termination false} SecurePageSpec extends IGeneratorCore {

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
      SecurePost(u, before, payload, after)
    }
  }
}
