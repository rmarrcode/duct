module DuctApi {

  datatype ReturnType = Content | Redirect

  datatype UserInfo = UserInfo(
    name: string,
    email: string,
    picture: string,
    authenticated: bool)

  trait {:termination false} IGenerator {

    ghost predicate PreCondition(u: UserInfo)
    ghost predicate PostCondition(u: UserInfo, html: string)

    method Generate(user: UserInfo) returns (content: string)
      requires PreCondition(user)
      ensures PostCondition(user, content)
  }

  class ApiEndpoint {
    
    var apiUrl: string;
    var returnType: ReturnType;
    var generator: IGenerator;

    constructor(apiUrl: string, rt: ReturnType, generator: IGenerator)
      requires apiUrl != ""
      requires apiUrl[0] == '/' // simple invariant: path-like
      requires generator != null
      ensures this.apiUrl == apiUrl
      ensures this.returnType == rt
      ensures this.generator == generator
    {
      this.apiUrl := apiUrl;
      this.returnType := rt;
      this.generator := generator;
    }
  }

  /// Collection of API endpoints.
  class AllApiEndpoints {
    var endpoints: seq<ApiEndpoint>

    constructor ()
      ensures endpoints == []
    {
      endpoints := [];
    }

    method Add(ep: ApiEndpoint)
      requires ep != null
      modifies this
      ensures endpoints == old(endpoints) + [ep]
    {
      endpoints := endpoints + [ep];
    }

    method Count() returns (n: int)
      ensures n == |endpoints|
    {
      n := |endpoints|;
    }

    method Get(i: int) returns (ep: ApiEndpoint)
      requires 0 <= i < |endpoints|
      ensures ep == endpoints[i]
    {
      ep := endpoints[i];
    }
  }
}

module SpecsTools {

  function Contains(haystack: string, needle: string): bool
    decreases |haystack|
  {
    if |needle| == 0 then true
    else if |haystack| < |needle| then false
    else haystack[0 .. |needle|] == needle || Contains(haystack[1..], needle)
  }

  lemma ContainsInserted(prefix: string, needle: string, suffix: string)
    ensures Contains(prefix + needle + suffix, needle)
    decreases |prefix|
  {
    if |needle| == 0 {
    } else if |prefix| == 0 {
      assert (prefix + needle + suffix)[0 .. |needle|] == needle;
    } else {
      assert (prefix + needle + suffix)[1..] == prefix[1..] + needle + suffix;
      ContainsInserted(prefix[1..], needle, suffix);
    }
  }

  lemma ContainsTail(haystack: string, needle: string)
    requires |haystack| > 0
    ensures Contains(haystack[1..], needle) ==> Contains(haystack, needle)
  {
  }

  lemma NoBarIfCharAbsent(s: string)
    requires '|' !in s
    ensures !Contains(s, "|")
    decreases |s|
  {
    if |s| > 0 {
      assert s[0] != '|';
      NoBarIfCharAbsent(s[1..]);
    }
  }

  lemma CrossingBarCannotMatch(left: string, right: string, needle: string)
    requires 0 < |needle|
    requires |left| < |needle|
    requires |needle| <= |left| + 1 + |right|
    requires !Contains(needle, "|")
    ensures (left + "|" + right)[0 .. |needle|] != needle
  {
    if (left + "|" + right)[0 .. |needle|] == needle {
      assert needle[|left| .. |left| + 1] == "|";
      assert needle == needle[..|left|] + "|" + needle[|left| + 1..];
      ContainsInserted(needle[..|left|], "|", needle[|left| + 1..]);
      assert Contains(needle, "|");
    }
  }

  lemma NoContainsJoinedByBar(left: string, right: string, needle: string)
    requires !Contains(left, needle)
    requires !Contains(right, needle)
    requires !Contains(needle, "|")
    ensures !Contains(left + "|" + right, needle)
    decreases |left|
  {
    if |needle| == 0 {
      assert false;
    } else if |left| == 0 {
      assert (left + "|" + right)[1..] == right;
      assert !Contains((left + "|" + right)[1..], needle);
      if |needle| <= |left| + 1 + |right| {
        CrossingBarCannotMatch(left, right, needle);
      }
    } else {
      assert (left + "|" + right)[1..] == left[1..] + "|" + right;
      if Contains(left[1..], needle) {
        ContainsTail(left, needle);
        assert false;
      }
      assert !Contains(left[1..], needle);
      NoContainsJoinedByBar(left[1..], right, needle);
      assert !Contains((left + "|" + right)[1..], needle);
      if |needle| <= |left| + 1 + |right| {
        if |left| < |needle| {
          CrossingBarCannotMatch(left, right, needle);
        } else {
          if (left + "|" + right)[0 .. |needle|] == needle {
            assert left[0 .. |needle|] == needle;
            assert Contains(left, needle);
          }
        }
      }
    }
  }

  function {:compile true} Link(linkLabel: string, url: string): string {
    "<a href=\"" + url + "\">" + linkLabel + "</a>"
  }

}
