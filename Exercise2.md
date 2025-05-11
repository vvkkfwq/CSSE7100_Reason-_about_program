## 练习 2.1

Determine how the following pairs of predicates are related, that is, which of the predicates is the weakest or strongest or if they are equivalent or if they are unrelated.

确定以下谓词对之间的关系，即哪个谓词是最弱的或最强的，或者它们是等价的或者它们之间没有关系。

> a) x <= 0 和 x <= 1

x <= 0 is stronger than x <= 1

> b) x > 0 && y > 0 和 x > 0

x > 0 && y > 0 is stronger than x > 0

> c) x > 0 || y > 0 和 x > 0

x > 0 || y > 0 is weaker than x > 0

> d) x >= 0 和 x*x + y*y == 9

unrealted

> e) x >= 1 ==> x >= 0 和 x >= 1

x >= 1 ==> x >= 0 is true for all values of x; an universally true predicate is weaker than any other predicate

so x >= 1 ==> x >= 0 is weaker than x >= 1

> f) (存在 i :: i >= 0 && x == i ) 和 x >= 1

exists i :: i >= 0 && x == i => x >= is weaker than x >= 1

> g) (存在 i :: P && Q) 和 (对于所有 i :: P ==> Q)

unrealted

情况 1：存在 i 使得 P(i) && Q(i) 成立，但 P(i) && !Q(i) 也成立
存在某些 i 使得 P(i) 成立且 Q(i) 也成立。

但对于其他的 i，P(i) 仍成立，而 Q(i) 却不成立，即 P(i) && !Q(i)。

结论：

(∃ i :: P(i) && Q(i)) 仍然为真（因为至少有一个 i 满足 P(i) && Q(i)）。

(∀ i :: P(i) ⇒ Q(i)) 为假（因为存在某个 i，满足 P(i) 但 Q(i) 不成立，违背了 P(i) ⇒ Q(i)）。

因此，(∀ i :: P(i) ⇒ Q(i)) 更强（Stronger），因为它要求所有 i 都满足 P(i) ⇒ Q(i)，但 ∃ i :: P(i) && Q(i) 只需要存在一个 i 满足。

情况 2：没有任何 i 满足 P(i)
也就是说，对于所有 i，P(i) 都是 false。

结论：

(∃ i :: P(i) && Q(i)) 为假（因为 P(i) && Q(i) 需要 P(i) 为真，而 P(i) 总是假，所以整个表达式为假）。

(∀ i :: P(i) ⇒ Q(i)) 为真（因为 P(i) ⇒ Q(i) 等价于 !P(i) || Q(i)，如果 P(i) 恒假，则 !P(i) 恒真，整个表达式自然为真）。

因此，(∃ i :: P(i) && Q(i)) 更强（Stronger），因为它要求至少存在一个 i 满足 P(i) && Q(i)，但 ∀ i :: P(i) ⇒ Q(i) 在 P(i) 恒假时自动成立。


## 练习 2.2

For each of the following triples, find initial values of x and y that demonstrate that the triple does not hold.

对于以下每组三元组，找到初始值 x 和 y，证明该三元组不成立。

> a) {true} x := 2*y {y <= x}

y < 0

> b) {x == 3} x := x + 1 {y == 4}

x == 3 && y != 4

> c) {true} x := 100 {false}

x == 100 && $\forall$y

> d) {x >= 0} x := x - 1 {x >= 0}

x == 0

## 练习 2.3

Compute the weakest precondition of the following statements with respect to the postcondition x + y < 100.

计算以下语句相对于后置条件 x + y < 100 的最弱前置条件。

> a) x := 32; y := 40

{{true}}

b) x := x + 2; y := y - 3*x

{{y - 2x < 104}}

c) x, y := x + 2, y - 3*x

$$
x + y < 100 => (x + 2) + y - 3*x < 100 => y - 2*x < 98
$$



## 练习 2.4

Verify that the following program correctly swaps x and y, where ^ denotes bitwise xor.

验证以下程序是否正确交换 x 和 y，其中 ^ 表示按位异或。

```dafny
x := x ^ y; 
y := x ^ y; 
x := x ^ y;
```

请注意，一个数字与自身的按位异或结果为 0，即 x ^ x = 0，并且一个数字与 0 的按位异或结果为该数字，即 x ^ 0 = 0 ^ x = x。

```dafny
{y == Y && x == X}

{y == Y && x ^ y ^ y == X}

{x == x ^ y}

{y == Y && x ^ y == X}

{0 ^ y == Y && x ^ y == X}

{x ^ x ^ y == Y && x ^ y == X}

{y == x ^ y}

{x ^ y == Y && y == X}

{x == x ^ y}

{x == Y && y == X}
```

## 练习 2.5

假设你希望在语句 `if x < 20 { y := 3; } else { y := 2; }` 之后满足 `x + y == 22`，那么在哪些状态下你可以开始该语句？换句话说，计算相对于 `x + y == 22` 的最弱前置条件。在计算完成后简化条件。

```
{x == 19} || {x == 20}
{x < 20 && x == 19} || {x >= 20 && x == 20}
{x < 20 ==> x == 19} && {x >= 20 ==> x == 20}
if x < 20 { 
  {x == 19}
  {x + 3 == 22}
  y := 3; 
  {x + y == 22}
} else { 
  {x == 20}
  {x + 2 == 22}
  y := 2;
  {x + y == 22}
}
{x + y == 22}
```

## 练习 2.6

计算相对于 `y < 10` 的最弱前置条件。简化条件。

```dafny
{x != 5}
{x >= 8 || x != 5}
{x < 8 ==> x != 5}
{(x < 8 ==> x != 5)} && true
{(x < 8 ==> x != 5) && (x >= 8 ==> true)}
if x < 8 {
  {x != 5}
  {x != 5 && true}
  {(x == 5 ==> false) && (x != 5 ==> true)}
  if x == 5 {
    {false} 
    {10 < 10}
    y := 10;
    {y < 10} 
  } else { 
    {true}
    {2 < 10}
    y := 2;
    {y < 10} 
  } 
} else { 
  {true}
  {0 < 10}
  y := 0; 
  {y < 10}
}
{y < 10}
```

## 练习 2.7

计算相对于 `y % 2 == 0`（即 "y 是偶数"）的最弱前置条件。简化条件。

```dafny
{x >= 10}
{x >= 10 || x >= 20}
{(x < 10 ==> x >= 20) && true}
{(x < 10 ==> x >= 20) && (x >= 10 && true)}
if x < 10 { 
  {x >= 20}
  {(x < 20 ==> false) && x >= 20 ==> true}
  if x < 20 { 
    {false}
    {1 % 2 == 0}
    y := 1;
    {y % 2 == 0}
  } else { 
    {true}
    {2 % 2 == 0}
    y := 2; 
    {y % 2 == 0}
  } 
} else { 
  {true}
  {4 % 2 == 0}
  y := 4;
  {y % 2 == 0}
}
{y % 2 == 0}
```

## 练习 2.8

确定在哪种情况下以下程序建立了 `0 <= y < 100`。如果你已经掌握了如何计算最弱前置条件，尝试心算。写下你得出的答案，然后写出完整的 wp 推理以检查你是否得到了正确的答案。

```dafny
{(x == 2 || x >= 34) && (x == 2 || x < 55)}
{x == 2 || (x >= 34 && x < 55)}
{(x < 34 && x == 2) || (x >= 34 && x < 55)}
{(x < 34 && x == 2) || (x >= 34 && x < 55)}
{(x < 34 ==> x == 2) && x >= 34 ==> x < 55}
if x < 34 { 
  {x == 2}
  {(x == 2 ==> -1 <= x < 99) && (x != 2 ==> false)}
  if x == 2 { 
    {-1 <= x < 99}
    {0 <= x + 1 < 100} 
    y := x + 1; 
    {0 <= y < 100} 
  } else { 
    {false}
    y := 233; 
    {0 <= y < 100} 
  } 
} else { 
  {x < 55}
  {x < 55 ==> true && x >= 55 ==> false}
  if x < 55 { 
    {true}
    y := 21; 
    {0 <= y < 100} 
  } else { 
    {false}
    y := 144; 
    {0 <= y < 100} 
  } 
}
{0 <= y < 100} 
```

## 练习 2.9

计算以下程序相对于后置条件 `x < 10` 的最弱前置条件。

```dafny
{(y < 7 || x % 2 == 1) ==> x < 10}
{(true && (y < 7 || x % 2 == 1)) ==> x < 10}
{((x % 2 == 0 || x % 2 == 1) && (y < 7 || x % 2 == 1)) ==> x < 10}
{((x % 2 == 0 && y < 7) || x % 2 == 1) ==> x < 10}
{(x % 2 == 0 && y < 7 ==> x < 10) && x % 2 == 1 ==> x < 10}
{(x % 2 == 0 ==> (y + 3 < 10 ==> x < 10) && !(x % 2 == 0) ==> x < 10)}
if x % 2 == 0 { 
  {y + 3 < 10 ==> x < 10}
  y := y + 3;
  {y < 10 ==> x < 10}
} else {
  {x < 10} 
  {true ==> x < 10}
  {4 < 10 ==> x < 10}
  y := 4; 
  {y < 10 ==> x < 10}
}
{y < 10 ==> x < 10}
{(y < 10 ==> x < 10) && true}
{(y < 10 ==> x < 10) && (y >= 10 ==> true)}
if y < 10 {
  {x < 10}
  y := x + y; 
  {x < 10}
} else { 
  {true}
  {8 < 10}
  x := 8;
  {x < 10} 
}
{x < 10}
```