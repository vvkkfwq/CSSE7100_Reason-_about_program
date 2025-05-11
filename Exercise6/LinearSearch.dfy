predicate Even(n: int) {
  n%2 == 0
}

method LinearSearch0<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    // look in postcondition (followed by using return)
  {
    if P(a[n]) { return; }
    n := n + 1;
  }
}

method LinearSearch1<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    // look in postcondition (followed by using return)
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    // replace a constant with a variable
  {
    if P(a[n]) { return; }
    n := n + 1;
  }
}

method TestLinearSearch(a:array<int>) returns (n: int)
  requires a.Length == 3
  requires a[0] == 1 && a[1]==2 && a[2] == 4
  ensures n == 1 || n == 2
{
  n := LinearSearch3<int>(a,Even);
}

method LinearSearch2<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures forall i :: 0 <= i < n ==> !P(a[i])
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    // look in postcondition (followed by using return)
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    // use postcondition
  {
    if P(a[n]) { return; }
    n := n + 1;
  }
}

method LinearSearch3<T>(a: array<T>, P: T -> bool) returns (n: int)
  requires exists i :: 0 <= i < a.Length && P(a[i])
  ensures 0 <= n < a.Length
  ensures P(a[n])
{
  n := 0;
  while true
    invariant 0 <= n < a.Length
    // look in postcondition (followed by using return)
    invariant exists i :: n <= i < a.Length && P(a[i])
    // use postcondition
    decreases a.Length - n
  {
    if P(a[n]) { return; }
    n := n + 1;
  }
}