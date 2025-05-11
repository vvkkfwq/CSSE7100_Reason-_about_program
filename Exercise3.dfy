method Mult(x: int, y: int) returns (r: int)
  requires x >= 0 && y >= 0
  ensures r == x * y
  decreases x
{
  // { x == 0 || x >= 1 && y >= 0 }             (A.22)
  // { x != 0 ==> x >= 1 && y >= 0 }            (A.9)
  // { true && (x != 0 ==> x >= 1 && y >= 0) }
  // { (x == 0 ==> 0 == x * y) && (x != 0 ==> x >= 1 && y >= 0) }
  if x == 0 {
    // { 0 == x * y}
    r := 0;
    // { r == x * y }
  } else {
    // { x >= 1 && y >= 0 }
    // { x - 1 >= 0 && y >= 0 }
    var z := Mult(x - 1, y);
    // { z == (x-1) * y }
    // { z + y == x * y }
    r := z + y;
    // { r == x * y }
  }
  // { r == x * y }
}

function F(x: int): int
  decreases x
{
  if x < 10 then x else F(x - 1)
}

// when x >= 10, x > x - 1 && x > 0 (beacuse x >= 10)

function G(x: int): int
  decreases x
{
  if x >= 0 then G(x - 2) else x
}

// when x >= 0, x > x - 2 && x >= 0 (if statement condition)

function H(x: int): int
  decreases x + 60
{
  if x < -60 then x else H(x - 1)
}

// when x < -60, x + 60 > (x - 1) + 60 && x + 6 >= 0

function I(x: nat, y: nat): int
  decreases x + y
{
  if x == 0 || y == 0 then 12 else if x%2 == y%2 then I(x - 1, y) else I(x, y - 1)
}

// when x and y are same parity, x + y > (x-1) + y
// when x and y are different parity, x + y > x + (y-1)

// when x + y >= 0 (because x and y are natural numbers)

function L(x: int): int
  decreases 100 - x
{
  if x < 100 then L(x + 1) + 10 else x
}

// when x < 100, 100 - x > 100 - (x + 1) && 100 - x >= 0

function J(x: nat, y: nat): int
  decreases 4*x + y
{
  if x == 0 then y else if y == 0 then J(x - 1, 3) else J(x, y - 1)
}
// when y == 0, 4*x + 0 > 4*(x-1) + 3 = 4*x - 4 + 3 = 4*x - 1
// when y != 0, 4*x + y > x + (y - 1) && x + y >= 0
