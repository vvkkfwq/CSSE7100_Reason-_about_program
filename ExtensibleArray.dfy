class ExtensibleArray<T(0)> {
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  const N: nat // size of front
  var length: nat // total number of elements in this
  var M: nat // the number of elements in the depot

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    // decreases Repr
  {
    // what's in Repr
    this in Repr && (front != null ==> front in Repr) &&
    (depot != null ==> depot in Repr && depot.Repr <= Repr &&
                       (forall j :: 0 <= j < |depot.Elements| ==> depot.Elements[j] in Repr) &&
                       // avoiding aliasing
                       {this, front} !! depot.Repr &&
                       (forall j :: 0 <= j < |depot.Elements| ==> depot.Elements[j] !in depot.Repr &&
                                                                  depot.Elements[j] != front && forall k :: 0 <= k < |depot.Elements| && k != j ==> depot.Elements[k] != depot.Elements[j]) &&
                       // ensuring depot is valid
                       depot.Valid()
    ) &&
    // abstraction relation
    N == 256 &&
    length == |Elements| &&
    M <= |Elements| < M + N &&
    (front == null <==> length == M) &&
    (front != null ==> front.Length == N) &&
    (depot != null ==> forall j :: 0 <= j < |depot.Elements| ==>
                                     depot.Elements[j].Length == N) &&
    M == (if depot == null then 0 else N*|depot.Elements|) &&
    (forall i :: 0 <= i <M ==> Elements[i] == depot.Elements[i/N][i%N]) &&
    (forall i :: M <= i < length ==> Elements[i] == front[i-M])
  }

  constructor ()
    ensures Valid() && fresh(Repr) && Elements == []
  {
    front, depot := null, null;
    M, length := 0, 0;
    N := 256;
    Elements := [];
    Repr := {this};
  }

  function Get(i: int): T
    requires Valid() && 0 <= i < |Elements|
    reads Repr
    ensures Get(i) == Elements[i]
  {
    if M <= i then front[i-M]
    else depot.Get(i/N)[i%N]
  }

  method Set(i: int, t: T)
    requires Valid() && 0 <= i < |Elements|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements)[i := t]
  {
    if M <= i {
      front[i-M] := t;
    } else {
      depot.Get(i/N)[i%N] := t;
    }
    Elements := Elements[i:=t];
  }

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements) + [t]
    decreases length
  {
    if front == null {
      front := new T[N];
      Repr := Repr + {front};
    }
    front[length-M] := t;
    length := length + 1;
    Elements := Elements + [t];
    if length == M + N {
      if depot == null {
        depot := new ExtensibleArray();
        // Repr := Repr + depot.Repr;
      }
      depot.Add(front);
      Repr := Repr + depot.Repr;
      M := M + N;
      front := null;
    }
  }
}