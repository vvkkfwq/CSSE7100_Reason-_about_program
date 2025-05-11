// Exercise 7.1
method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i,j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  var m := 0;
  while m != a.Length0
    invariant 0 <= m <= a.Length0 // bounds on m
    invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
    invariant forall i,j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
  {
    var n := 0;
    while n != a.Length1
      invariant 0 <= n <= a.Length1
      invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
      invariant forall j :: 0 <= j < n ==> a[m,j] == old(a[m,j]) + 1
      invariant forall i,j :: m < i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
      invariant forall j :: n <= j < a.Length1 && 0 <= j < a.Length1 ==> a[m,j] == old(a[m,j])
    {
      a[m,n] := a[m,n] + 1;
      n := n + 1;
    }
    m := m + 1;
  }
}

// Exercise 7.2
method Copymatrix(src: array2, dst: array2)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < dst.Length0 && 0 <= j < dst.Length1 ==> dst[i,j] == old(src[i,j])
{
  var m := 0;
  while m != src.Length0
    invariant 0 <= m <= src.Length0
    invariant forall i,j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
    invariant forall i,j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i,j] == old(src[i,j])
  {
    var n := 0;
    while n != src.Length1
      invariant 0 <= n <= src.Length1
      invariant forall i,j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
      invariant forall j :: 0 <= j < n ==> dst[m,j] == old(src[m,j])
      invariant forall i,j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i,j] == old(src[i,j])
    {
      dst[m,n] := src[m,n];
      n := n + 1;
    }
    m := m + 1;
  }
}

// Exercise 7.3
method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2*old(src[i])
{
  var n := 0;
  while n != src.Length
    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == 2*old(src[i])
    invariant forall i :: n <= i < src.Length ==> src[i] == old(src[i])
  {
    dst[n] := 2*src[n];
    n := n + 1;
  }
}

// Exercise 7.4
method Rotateleft(a: array)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[i+1])
  ensures a[a.Length - 1] == old(a[0])
{
  var n := 0;
  while n != a.Length-1
    invariant 0 <= n <= a.Length-1
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i+1])
    invariant a[n] == old(a[0])
    invariant forall i :: n < i a.Length ==> a[i] == old(a[i])
  {
    a[n],a[n+1] := a[n+1],a[n];
    n := n +1;
  }
}