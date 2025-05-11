method CommonElement(r: array<int>, x: array<int>) returns (b: bool)
  requires forall i, j :: 0 <= i < j < x.Length ==> x[i] <= x[j]
  ensures b <==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
{
  b := false;
  var n := 0;
  while n != r.Length && !b
    invariant 0 <= n <= r.Length // bounds for n
    invariant b <==>
              exists i, j :: 0 <= i < n && 0 <= j < x.Length && r[i] == x[j]
    // replace a constant by a variable
  {
    var m := 0;
    while m != x.Length && !b && x[m] <= r[n]
      invariant 0 <= m <= x.Length // bounds for m
      invariant b <==> exists i, j :: 0 <= i < n+1 && 0 <= j < m && r[i] == x[j]
      // replace a constant by a variable
    {
      if r[n] == x[m] {
        b := true;
      }
      m := m +1;
    }
    // b <==> exists i, j :: 0 <= i < n+1 && 0 <= j < x.Length && r[i] == x[j]
    n:= n + 1;
    // b <==> exists i, j :: 0 <= i < n && 0 <= j < x.Length && r[i] == x[j]
  }
}