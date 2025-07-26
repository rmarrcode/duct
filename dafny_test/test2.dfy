method Sort(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
  var n := a.Length;
  var i := 0;

  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
    invariant forall k, l :: 0 <= k < i <= l < n ==> a[k] <= a[l]
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> a[i] <= a[k]
      invariant forall k :: 0 <= k < i ==> a[k] <= a[i]
    {
      if a[j] < a[i] {
        var tmp := a[i];
        a[i] := a[j];
        a[j] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
