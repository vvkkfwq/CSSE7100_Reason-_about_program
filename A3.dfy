class Stack<T(0)> {
  ghost var s: seq<T>
  ghost const max: nat
  ghost var Repr: set<object>
  var a: array<T>
  var top: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |s| <= max
  {
    this in Repr && a in Repr &&
    a.Length == max && top <= max &&
    s == a[top..]
  }

  constructor (max: nat)
    ensures Valid() && fresh(Repr)
    ensures s == [] && this.max == max
  {
    s := [];
    this.max := max;
    a := new T[max];
    top := max;
    Repr := {this, a};
  }

  function Size(): nat
    requires Valid()
    reads Repr
    ensures Size() == |s|
  {
    a.Length - top
  }

  method Push(v: T)
    requires Valid()
    requires |s| < max
    modifies Repr
    ensures s == [v] + old(s)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    top := top - 1;
    a[top] := v;
    s := [v] + old(s);
  }

  method Pop() returns (v: T)
    requires s != []
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures v == old(s[0]) && s == old(s[1..])
  {
    v := a[top];
    top := top + 1;
    s := s[1..];
  }
}

class Deque<T(0)> {
  ghost var q: seq<T>
  ghost const max: nat
  ghost var Repr: set<object>
  var a: array<T>
  var front: nat
  var back: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |q| <= max
  {
    this in Repr && a in Repr &&
    a.Length == max + 1 && front <= max && back <= max &&
    (back == front - 1 ==> q == []) &&
    (front == 0 && back == max ==> q == []) &&
    (front <= back && !(front == 0 && back == max) ==> q == a[front..back + 1]) &&
    (front > back && !(back == front - 1) ==> q == a[front..] + a[..back + 1])
  }

  constructor (max: nat)
    ensures q == [] && this.max == max
    ensures Valid() && fresh(Repr)
  {
    q := [];
    this.max := max;
    a := new T[max + 1];
    front := 0;
    back := max;
    Repr := {this, a};
  }

  function Size(): nat
    requires Valid()
    reads Repr
    ensures Size() == |q|
  {
    if back == front - 1 then
      0
    else if front == 0 && back == a.Length - 1 then
      0
    else if front <= back then
      back - front + 1
    else
      a.Length - front + back + 1
  }

  method AddBack(x:T)
    requires Valid()
    requires |q| < max
    modifies Repr
    ensures q == old(q) + [x]
    ensures max == old(max)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    if back == a.Length - 1 {
      back := 0;
    } else {
      back := back + 1;
    }
    a[back] := x;
    q := old(q) + [x];
  }

  method AddFront(x:T)
    requires Valid()
    requires |q| < max
    modifies Repr
    ensures q == [x] + old(q)
    ensures max == old(max)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    if front == 0 {
      front := a.Length - 1;
    } else {
      front := front - 1;
    }
    a[front] := x;
    q := [x] + old(q);
  }

  method RemoveBack() returns (x:T)
    requires Valid()
    requires |q| != 0
    modifies Repr
    ensures q == old(q[..|q| - 1]) && x == old(q[|q| - 1])
    ensures max == old(max)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    q := q[..|q| - 1];
    x := a[back];
    if back == 0 {
      back := a.Length - 1;
    } else {
      back := back - 1;
    }
  }

  method RemoveFront() returns (x:T)
    requires Valid()
    requires |q| != 0
    modifies Repr
    ensures q == old(q[1..]) && x == old(q[0])
    ensures max == old(max)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    q := q[1..];
    x := a[front];
    if front == a.Length - 1 {
      front := 0;
    } else {
      front := front + 1;
    }
  }
}

class MidStack<T(0)> {
  ghost var s: seq<T>
  ghost const max: nat
  ghost var Repr: set<object>
  var stack: Stack<T>
  var deque: Deque<T>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |s| <= max
  {
    this in Repr && stack in Repr && deque in Repr &&
    deque.Repr <= Repr && stack.Repr <= Repr &&
    deque.Repr !! stack.Repr !! {this} &&
    stack.Valid() && deque.Valid() &&
    s == deque.q + stack.s && |s| <= max &&
    (|s| % 2 == 0 ==> |deque.q| == |stack.s|) && (|s| % 2 == 1 ==> |deque.q| == |stack.s| + 1) &&
    (max % 2 == 0 ==> deque.max == stack.max == max / 2 ) &&
    (max % 2 == 1 ==> deque.max ==max / 2 + 1 && stack.max == max / 2)
  }

  constructor (max: nat)
    ensures Valid() && fresh(Repr)
    ensures s == [] && this.max == max
  {
    s := [];
    this.max := max;
    if max % 2 == 0 {
      stack := new Stack<T>(max/2);
      deque := new Deque<T>(max/2);
    } else {
      stack := new Stack<T>(max/2);
      deque := new Deque<T>(max/2+1);
    }
    new;
    Repr := {this, stack, deque} + deque.Repr + stack.Repr;
  }

  function Size(): nat
    requires Valid()
    reads Repr
    ensures Size() == |s|
  {
    stack.Size() + deque.Size()
  }

  method Push(x: T)
    requires Valid()
    requires |s| < max
    modifies Repr
    ensures s == [x] + old(s)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    if deque.Size() > stack.Size() {
      var moved := deque.RemoveBack();
      stack.Push(moved);
    }
    deque.AddFront(x);
    s := [x] + old(s);
    Repr := Repr + deque.Repr + stack.Repr;
  }

  method Pop() returns (x:T)
    requires Valid()
    requires |s| > 0
    modifies Repr
    ensures x == old(s[0]) && s == old(s[1..])
    ensures Valid() && fresh(Repr - old(Repr))
  {
    x := deque.RemoveFront();
    s := old(s[1..]);
    if deque.Size() < stack.Size() {
      var moved := stack.Pop();
      deque.AddBack(moved);
    }
    Repr := Repr + deque.Repr + stack.Repr;
  }

  method PopMiddle() returns (x: T)
    requires Valid()
    requires |s| > 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures x == old(s[|s|/2])
    ensures s == old(s[..|s|/2]) + old(s[|s|/2+1..])
  {
    if deque.Size() > stack.Size() {
      x := deque.RemoveBack();
    } else {
      x := stack.Pop();
    }
    s := deque.q + stack.s;
    Repr := Repr + deque.Repr + stack.Repr;
  }
}

