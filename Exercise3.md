# Exercise 3

## Exercise 3.1  

(a) Show that the following method is partially correct by supplying a weakest precondition proof.  

```dafny
method Mult(x: int, y: int) returns (r: int)
  requires x >= 0 && y >= 0
  ensures r == x * y
{
  { x == 0 || x >= 1 && y >= 0 }             (A.22)
  { x != 0 ==> x >= 1 && y >= 0 }            (A.9)
  { true && (x != 0 ==> x >= 1 && y >= 0) }
  { (x == 0 ==> 0 == x * y) && (x != 0 ==> x >= 1 && y >= 0) }
  if x == 0 {
    { 0 == x * y}
    r := 0;
    { r == x * y }
  } else {
    { x >= 1 && y >= 0 }
    { x - 1 >= 0 && y >= 0 }
    var z := Mult(x - 1, y);
    { z == (x-1) * y }
    { z + y == x * y }
    r := z + y;
    { r == x * y }
  }
  { r == x * y }
}
```

(b) Provide a termination metric to show that it is totally correct.

```dafny
method Mult(x: int, y: int) returns (r: int)
  requires x >= 0 && y >= 0
  ensures r == x * y
  decreases x // add decreases x
{
  if x == 0 {
    r := 0;
  } else {
    var z := Mult(x - 1, y);
    r := z + y;
  }
}
```

## Exercise 3.2

Write a simple decreases clause (one that is not a lexicographic tuple) that proves termination for each of the following functions.  
For integers, `X` decreases to `x` when `X > x && X >= 0`.

a)

```dafny
function F(x: int): int
  decreases x
{
  if x < 10 then x else F(x - 1)
}
```

b)

```dafny
function G(x: int): int 
  decreases x
{
  if x >= 0 then G(x - 2) else x
}
```

c)

```dafny
function H(x: int): int 
  decreases x + 60
{
  if x < -60 then x else H(x - 1)
}
```

d)

```dafny
function I(x: nat, y: nat): int 
  decreases x + y
{
  if x == 0 || y == 0 then 12 
  else if x % 2 == y % 2 then I(x - 1, y) 
  else I(x, y - 1)
}
```

e)

```dafny
function L(x: int): int 
  decreases 100 - x
{
  if x < 100 then L(x + 1) + 10 else x
}
```

f)

```dafny
function J(x: nat, y: nat): int 
  
{
  if x == 0 then y 
  else if y == 0 then J(x - 1, 3) 
  else J(x, y - 1)
}
```

## Exercise 3.3

Determine if the first tuple exceeds the second.

a) 2, 5 and 1, 7  
b) 1, 7 and 7, 1  
c) 5, 0, 8 and 4, 93  
d) 4, 9, 3 and 4, 93  
e) 4, 93 and 4, 9, 3  
f) 3 and 2, 9  
g) true, 80 and false, 66  
h) 4, true, 50 and 4, false, 800  

Exercise 3.4.  
Add decreases clauses to prove termination of the following mutually recursive methods.

a)

```dafny
method Outer(a: nat) {
  if a != 0 {
    var b := a - 1;
    Inner(a, b);
  }
}

method Inner(a: nat, b: nat)
  requires a != 0
{
  if b == 0 {
    Outer(a - 1);
  } else {
    Inner(a, b - 1);
  }
}
```

b)

```dafny
method Outer(a: nat) {
  if a != 0 {
    var b := a - 1;
    Inner(a - 1, b);
  }
}

method Inner(a: nat, b: nat) {
  if b == 0 {
    Outer(a);
  } else {
    Inner(a, b - 1);
  }
}
```
