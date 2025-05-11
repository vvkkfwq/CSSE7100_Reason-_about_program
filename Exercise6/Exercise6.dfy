// Exercise 6.1
method LinearSearch2<T>(a: array<T>, P: T -> bool) returns (n: int)
  // a)
  ensures -1 <= n < a.Length
  ensures n == -1 || P(a[n])
  ensures forall i :: 0 <= i < n ==> !P(a[i])
  ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{
  n := 0;
  while n != a.Length
    // b)
    invariant -1 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    // c)
  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
  n := -1;
}

// Exercise 6.2
method Max(a: array<nat>) returns (m: int)
  ensures (exists i :: 0 <= i < a.Length && m == a[i]) || (a.Length == 0 && m == -1)
  ensures forall i :: 0 <= i < a.Length ==> m >= a[i]
{
  m := -1;
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] <= m // Loop technique 3
    invariant (exists i :: 0 <= i < a.Length && m == a[i]) || (m == -1 && n == 0) // Loop technique 3
  {
    if a[n] > m {
      m := a[n];
    }
    n := n + 1;
  }
}

// Exercise 6.3
method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] <= key
  ensures forall i :: n <= i < a.Length ==> key < a[i]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] <= key
    invariant forall i :: hi <= i < a.Length ==> key < a[i]
  {
    var mid := (lo + hi) / 2;
    if a[mid] <= key {
      // need to check right of mid - update lo
      lo := mid+1;
    } else { // a[mid] >= key
      // either we've found key or need to check left of mid - update hi
      hi := mid;
    }
  }
  // {lo >= hi && 0 <= lo <= a.Length && forall i :: 0 <= i < lo ==> a[i] < key && forall i :: hi <= i < a.Length ==> key <= a[i]} // merge ranges
  // {lo >= hi && lo <= hi && 0 <= lo <= a.Length && forall i :: 0 <= i < lo ==> a[i] < key && forall i :: hi <= i < a.Length ==> key <= a[i]} // replace lo == hi with lo >= hi && lo <= hi
  // {lo == hi && 0 <= lo <= a.Length && forall i :: 0 <= i < lo ==> a[i] < key && forall i :: hi <= i < a.Length ==> key <= a[i]} // replace hi with lo
  // {lo == hi && 0 <= lo <= a.Length && forall i :: 0 <= i < lo ==> a[i] < key && forall i :: lo <= i < a.Length ==> key <= a[i]} // strengthen with lo == hi
  // {0 <= lo <= a.Length && forall i :: 0 <= i < lo ==> a[i] < key && forall i :: lo <= i < a.Length ==> key <= a[i]}
  n := lo;
  // {0 <= n <= a.Length && forall i :: 0 <= i < n ==> a[i] < key && forall i :: n <= i < a.Length ==> key <= a[i]}
}