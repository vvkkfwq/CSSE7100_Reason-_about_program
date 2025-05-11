// Technique 1
// method SquareRoot(N: nat) returns (r: nat)
//   ensures r*r <= N && N < (r + 1)*(r + 1)
// {
//   // { 0 < = N}
//   // {0*0 <= N}
//   r := 0;
//   // {r*r <= N}
//   while (r + 1)*(r + 1) <= N
//     invariant r*r <= N
//   {
//     // { (r+1)*(r+1) <= N && r*r <= N}             // strengthen
//     // { (r+1)*(r+1) <= N }
//     r := r + 1;
//     // { r*r <= N}
//   }
//   // {r*r <= N && N < (r + 1)*(r + 1)
// }

// Technique 2
// method SquareRoot(N: nat) returns (r: nat)
//   ensures r*r <= N && N < (r + 1)*(r + 1)
// {
//   r := 0;
//   var s := 1;
//   while s <= N
//     invariant r*r <= N
//     invariant s == (r + 1)*(r + 1)
//   {
//     // {r*r <= N && s == (r + 1)*(r + 1)}                         // strengthen
//     // {(r+1)*(r+1) <= N && s == (r + 1)*(r + 1)}
//     // {(r+1)*(r+1) <= N && s + 2*r + 3 == (r + 1)*(r + 1) + 2*r + 3}
//     s := s + 2*r + 3;
//     // {(r+1)*(r+1) <= N && s == (r + 1)*(r + 1) + 2*r + 3}
//     // {(r+1)*(r+1) <= N && s == r*r + 2*r + 1 + 2*r + 3}
//     // {(r+1)*(r+1) <= N && s == r*r + 4*r + 4}
//     // {(r+1)*(r+1) <= N && s == (r + 2)*(r + 2)}
//     // {(r+1)*(r+1) <= N && s == (r + 1 + 1)*(r + 1 + 1)}
//     r := r + 1;
//     // {r*r <= N && s == (r + 1)*(r + 1)}
//   }
//   // {r*r <= N && N < (r + 1)*(r + 1)}
// }

ghost function Fib(n: nat): nat {
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

// method ComputeFib(n: nat) returns (x: nat)
//   ensures x == Fib(n)
// {
//   x := 0;
//   var i := 0;
//   while i != n
//     invariant 0 <= i <= n
//     invariant x == Fib(i)
//   {
//     // { 1 <= i < n && x == Fib(i) + Fib(i – 1) }      // definition of Fib, but 1 <= i < n is too strong so that can't reach 0 <= n  at top of loop body, so we should use a new way
//     // {1 <= i < n && x == Fib(i + 1)}                 // strengthen 1 <= i, because when i == -1 or 0, Fib(i) + Fib(i – 1) will not be defined
//     // {-1 <= i <= n - 1 && x == Fib(i + 1)}
//     // {-1 <= i <= n - 1 && x == Fib(i + 1)}
//     // {0 <= i + 1 <= n && x == Fib(i + 1)}
//     i := i + 1;
//     // {0 <= i <= n && x == Fib(i)}
//   }
//   // {x == Fib(n)}
// }

// wish y == Fib(i + 1)
method ComputeFib(n: nat) returns (x: nat)
  ensures x == Fib(n)
{
  x := 0;
  var y := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant x == Fib(i) && y == Fib(i + 1)
  {
    // { i != n && 0 <= i <= n && x == Fib(i) && y == Fib(i + 1) }
    // { 0 <= i < n && x == Fib(i) && y == Fib(i + 1) }
    // { 0 <= i < n && y == Fib(i + 1) && x + y == Fib(i) + Fib(i + 1) }
    x, y := y, x + y;
    // { 0 <= i < n && x == Fib(i + 1) && y == Fib(i) + Fib(i + 1) }                  // strengthen by removing -1 from  the possible values for i
    // { -1 <= i <= n – 1 && x == Fib(i + 1) && y == Fib(i) + Fib(i + 1) }
    // { -1 <= i <= n - 1 && x == Fib(i + 1) && y == Fib(i + 2) }
    // { 0 <= i + 1 <= n && x == Fib(i + 1) && y == Fib(i + 2) }
    // { 0 <= i + 1 <= n && x == Fib(i + 1) && y == Fib(i + 1 + 1) }
    i := i + 1;
    // { 0 <= i <= n && x == Fib(i) && y == Fib(i + 1) }
  }
  // {x == Fib(n)}
}

// Technique 3
ghost function Power(n: nat): nat {
  if n == 0 then 1 else 2*Power(n-1)
}

method ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
{
  p := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant p == Power(i)                   // n replace as i
  {
    // { 0 <= i <= n && p == Power(i) && i != n } (arithmetic)
    // { 0 <= i < n && 2*p == 2*Power(i) }
    p := 2*p;
    // { 0 <= i < n && p == 2*Power(i) } (definition of Power)
    // { 0 <= i < n && p == Power(i + 1) } (strengthen 0 <= i)
    // { 0 <= i + 1 <= n && p == Power(i + 1) }
    i := i + 1;
    // { 0 <= i <= n && p == Power(i)}
  }
}