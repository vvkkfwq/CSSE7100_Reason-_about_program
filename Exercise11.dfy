class Stack<T> {
  ghost var s: seq<T>
  ghost var Repr: set<object>
  var top: Node?<T>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (top == null ==> s == []) &&
    (top != null ==> top in Repr && top.Repr <= Repr && this !in top.Repr &&
                     top.Valid() && top.s == s)
  }

  constructor()
    ensures Valid() && fresh(Repr)
    ensures s == []
  {
    top := null;
    s, Repr := [], {this};
  }

  method Push(v: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures s == [v] + old(s)
  {
    var newNode := new Node(v);
    if top != null {
      newNode.SetNext(top);
    }
    top := newNode;
    s, Repr := [v] + s, {this} + newNode.Repr;
  }
  method Pop() returns (v: T)
    requires s != []
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures v == old(s[0]) && s == old(s[1..])
  {
    v := top.GetValue();
    top := top.GetNext();
    s := s[1..]; // note that the removal of old(top) from Repr is not required
  }
}

class Node<T> {
  ghost var s: seq<T>
  ghost var Repr: set<object>
  var value: T
  var next: Node?<T>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |s| > 0
  {
    this in Repr &&
    (next == null ==> s == [value]) &&
    (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr &&
                      next.Valid() && s == [value] + next.s)
  }
  constructor (v: T)
    ensures Valid() && fresh(Repr)
    ensures s == [v]
  {
    value := v;
    next := null;
    s, Repr := [v], {this};
  }
  method SetNext(n: Node<T>)
    requires Valid() && n.Valid() && this !in n.Repr && n.Repr !! Repr
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr) - n.Repr)
    ensures s == old([s[0]]) + n.s
  {
    next := n;
    s, Repr := [value] + n.s, Repr + next.Repr;
  }
  method GetNext() returns (n: Node?<T>) // could also be a function
    requires Valid()
    ensures n == null ==> |s| == 1
    ensures n != null ==> n in Repr && n.Repr <= Repr && this !in n.Repr &&
                          n.Valid() && s == [s[0]] + n.s
  {
    n := next;
  }
  method GetValue() returns (v: T) // could also be a function
    requires Valid()
    ensures v == s[0]
  {
    v := value;
  }
}