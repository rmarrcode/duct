module UserInfoSpecs {

  import opened Tools
  import opened DB

  function DigitString(d: nat): string
    requires d < 10
  {
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
  }

  function NatToString(n: nat): string
  {
    if n < 10 then DigitString(n) else NatToString(n / 10) + DigitString(n % 10)
  }

  predicate UserInfoPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    payload == Content(NatToString(|before|)) &&
    after == before
  }

  trait {:termination false} UserInfoSpec extends IGeneratorCore {

    predicate PreCondition(u: UserInfo)
    {
      true
    }

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>
    )
    {
      UserInfoPost(u, before, payload, after)
    }
  }
}
