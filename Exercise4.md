# Exercise 4.1

For each of the following uses of loop specifications, indicate whether or not the loop's initial proof obligation is met and whether or not the postcondition following the loop can be proved to hold.

### a)

```dafny
x := 0;
while x != 100
  invariant true
{
  x == 100
}
```

> Is the loop's initial proof obligation met?

Yes (invariant is true)

> Is the postcondition following the loop provable?

Yes { true && x == 100 } => { x == 100 }

### b)

```dafny
x := 20;
while 10 < x
  invariant x%2 == 0
{
  x == 10
}
```

> Is the loop's initial proof obligation met?

Yes (invariant is x%2 == 0)

> Is the postcondition following the loop provable?

No { x <= 10 && x%2 == 0 } => { x == 10 or x == 8 or x == 6 or x == 4 or x == 2 or x == 0 }

### c)

```dafny
x := 20;
while x < 20
  invariant x%2 == 0
{
  x == 20
}
```

> Is the loop's initial proof obligation met?

Yes (invariant is x%2 == 0)

> Is the postcondition following the loop provable?

No { x >= 20 && x % 2 == 0 } => { x == 20 or x == 22 or x == 24 or x == 26 or x == 28 or x == 30 }

### d)

```dafny
x := 3;
while x < 2
  invariant x%2 == 0
{
  x%2 == 0
}
```

> Is the loop's initial proof obligation met?

No ( x%2 == 0 is not true)

> Is the postcondition following the loop provable?

Yes { x >= 2 && x%2 == 0 } => { x % 2 == 0 }

### e)

```dafny
x := 0;
while x < 100
  invariant 0 <= x < 100
{
  x == 25
}
```

> Is the loop's initial proof obligation met?

Yes (invariant is 0 <= x < 100)

> Is the postcondition following the loop provable?

Yes { x >= 100 && 0 <= x < 100 } == { false } => { x == 25 } (A.30)

# Exercise 4.2

For each program, determine why the postcondition is not provable and strengthen the invariant so that it holds on entry to the loop and suffices to prove the postcondition.

### a)

```dafny
i := 0;
while i < 100
  invariant 0 <= i
{
  i == 100
}
```

> Why the postcondition is not provable?

The invariant is not strong enough to prove the postcondition.
`{ i >= 100 && 0 <= i } => { i == 100 }` is not valid.
`{ i >= 100 && 0 <= i }` is false when `i < 100`.
**Strengthen the invariant**: `0 <= i <= 100`

### b)

```dafny
i := 100;
while i > 0
  invariant true
{
  i == 0
}
```

> Why the postcondition is not provable?

The invariant is not strong enough to prove the postcondition.
`{ i <= 0 && true } => { i <= 0 }` is not valid.
`{ i <= 0 && true }` is false when `i > 0`.
**Strengthen the invariant**: `0 <= i`

### c)

```dafny
i := 0;
while i < 97
  invariant 0 <= i <= 99
{
  i == 99
}
```

> Why the postcondition is not provable?

The invariant is not strong enough to prove the postcondition.
`{ i >= 97 && 0 <= i < 99 } => { 97 <= i <= 99 }` is not valid.
**Strengthen the invariant**: `0 <= i <= 99 && i % 9 == 0`

### d)

```dafny
i := 22;
while i%5 != 0
  invariant 10 <= i <= 100
{
  i == 55
}
```

> Why the postcondition is not provable?

The invariant is not strong enough to prove the postcondition.
`{ i % 5 == 0 && 10 <= i <= 100 } => { i == 55 }` is not valid.
**Strengthen the invariant**: `10 <= i <= 100 && i % 11 == 0`

# Exercise 4.3

Consider the following program fragment:

```dafny
x := 0;
while x < 100
{
  x := x + 3;
}
{ x == 102 }
```

Write a loop invariant that holds initially, is maintained by the loop body, and allows you to prove the postcondition after the loop.

```dafny
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
```

# Exercise 4.4

For each of the following methods, write a loop invariant and a decreases clause that would allow you to prove the method is totally correct. The proof is not required.

### method UpWhileLess

```dafny
method UpWhileLess(N: int) returns (i: int)
  requires N >= 0
  ensures i == N
{
  i := 0;
  while i < N {
    i := i + 1;
  }
}
```

Loop invariant:

```dafny
invariant 0 <= i <= N
```

Decreases clause:

```dafny
decreases N - i
```

### method UpWhileNotEqual

```dafny
method UpWhileNotEqual(N: int) returns (i: int)
  requires N >= 0
  ensures i == N
{
  i := 0;
  while i != N {
    i := i + 1;
  }
}
```

Loop invariant:

```dafny
invariant 0 <= i <= N
```

Decreases clause:

```dafny
decreases N - i
```

### method DownWhileNotEqual

```dafny
method DownWhileNotEqual(N: int) returns (i: int)
  requires N >= 0
  ensures i == 0
{
  i := N;
  while i != 0 {
    i := i - 1;
  }
}
```

Loop invariant:

```dafny
invariant 0 <= i <= N
```

Decreases clause:

```dafny
decreases i
```

### method DownWhileGreater

```dafny
method DownWhileGreater(N: int) returns (i: int)
  requires N >= 0
  ensures i == 0
{
  i := N;
  while i > 0 {
    i := i - 1;
  }
}
```

Loop invariant:

```dafny
invariant 0 <= i <= N
```

Decreases clause:

```dafny
decreases i
```

# Exercise 4.5

Let Power be defined as

```dafny
ghost function Power(n: nat): nat {
  if n == 0 then 1 else 2*Power(n - 1)
}
```

and ComputePower be the method

```dafny
method ComputePower(N: int) returns (y: nat)
  requires N >= 0
  ensures y == Power(N)
{
  y := 1;
  var x := 0;
  while x != N
    invariant 0 <= x <= N
    invariant y == Power(x)
  {
    x, y := x + 1, y + y;
  }
}
```

### a)

Use weakest precondition reasoning to show that ComputePower is partially correct.

### b)

Use weakest precondition reasoning to show that ComputePower is totally correct.

```dafny
while (x != N)
invariant 0 <= x <= N
invariant y == Power(x)
decreases N - x
{
  // The invariant 0 <= x <= N is maintained because x increments by 1 until it equals N.
  // The invariant y == Power(x) is maintained because y doubles at each step, matching Power(x).
  ghost var d := N - x;
  // The decreases clause N - x ensures termination because d decreases by 1 at each step.
  assert d >= 0; // d starts at N and decreases to 0.
  x, y := x + 1, y + y;
}
The method terminates since N - x >= 0 is implied by the invariant and decreases to 0.
```
