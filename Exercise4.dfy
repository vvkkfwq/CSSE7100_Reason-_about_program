method F() returns (x: int)
  ensures x == 102
{
  x := 0;
  while x < 100
    invariant x <= 102 && x % 3 == 0
  {
    x := x + 3;
  }
}

method UpWhileLess(N: int) returns (i: int)
  requires N >= 0
  ensures i == N
  // decreases N - i
{
  i := 0;
  while i < N
    invariant i <= N
  {
    i := i + 1;
  }
}

method UpWhileNotEqual(N: int) returns (i: int)
  requires N >= 0
  ensures i == N
  // decreases N - i
{
  i := 0;
  while i != N
    invariant 0 <= i <= N
  {
    i := i + 1;
  }
}

method DownWhileNotEqual(N: int) returns (i: int)
  requires N >= 0
  ensures i == 0
  // decreases i
{
  i := N;
  while i != 0
    invariant i >= 0
  {
    i := i - 1;
  }
}

method DownWhileGreater(N: int) returns (i: int)
  requires N >= 0
  ensures i == 0
{
  i := N;
  while i > 0
    invariant i >= 0
  {
    i := i - 1;
  }
}

ghost function Power(n: nat): nat {
  if n == 0 then 1 else 2*Power(n - 1)
}

method ComputePower(N: int) returns (y: nat)
  requires N >= 0
  ensures y == Power(N)
{
  y := 1;
  var x := 0;
  while (x != N)
    invariant 0 <= x <= N
    invariant y == Power(x)
    decreases N - x
  {

    var WP: bool;
    var WP_s: bool;
    WP := N - x >= 0;
    WP := true && N - x >= 0;
    WP := N - x > N - (x+1) && N - x >= 0;
    var d := N - x;
    WP := d > N - (x+1) && d >= 0;
    x, y := x + 1, y + y;
    WP := d > N - x && d >= 0;
  }
}