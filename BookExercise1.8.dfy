// Here is the type signature of a method to compute s to be the sum of x and y and m to be the maximum of x and y:
method MaxSum(x: int, y: int) returns (s: int, m: int)
{
  s := x + y;
  if (x > y) {
    m := x;
  } else {
    m := y;
  }
}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m


method TestMaxSum(x: int, y: int)
{
  var s, m := MaxSum(x, y);
  var xx, yy := ReconstructFromMaxSum(s, m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}