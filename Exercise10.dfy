// Exercise10.1
class UniqueNumberAllocator {
  ghost var used: set<nat>
  var next: nat

  ghost predicate Valid()
    reads this
  {
    // built relation between next and used: used = {0, 1, 2, ..., next - 1}
    forall n :: 0 <= n < next <==> n in used
  }
  constructor ()
    ensures Valid() && used == {}
  {
    //Initialize the allocator
    next := 0;
    used := {};
  }

  method Allocate() returns (n: nat)
    requires Valid()
    modifies this
    ensures Valid() && n !in old(used) && used == old(used) + {n}
  {
    n := next;
    next := next + 1;
    used := used + {n};
  }

  method Reset()
    requires Valid()
    modifies this
    ensures Valid() && used == {}
  {
    next := 0;
    used := {};
  }
}

// Exercise10.2
class Grinder {
  ghost var hasBeans: bool
  ghost var Repr: set<object>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr

  constructor()
    ensures Valid() && fresh(Repr) && !hasBeans

  function Ready(): bool
    requires Valid()
    reads Repr
    ensures Ready() == hasBeans

  method AddBeans()
    requires Valid()
    modifies Repr
    ensures Valid() && hasBeans && fresh(Repr-old(Repr))

  method Grind()
    requires Valid() && hasBeans
    modifies Repr
    ensures Valid() && fresh(Repr-old(Repr))
}

class WaterTank {
  ghost var waterLevel: nat
  ghost var Repr: set<object>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr

  constructor()
    ensures Valid() && fresh(Repr) && waterLevel == 0

  function Level(): nat
    requires Valid()
    reads Repr
    ensures Level() == waterLevel

  method Fill()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == 10

  method Use()
    requires Valid() && waterLevel != 0
    modifies Repr
    ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == old(waterLevel) - 1
}

class CoffeeMaker {
  ghost var ready: bool
  ghost var Repr: set<object>
  var g: Grinder
  var w: WaterTank

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr && g in Repr && w in Repr &&
    g.Repr <= Repr && w.Repr <= Repr &&
    w.Repr !! g.Repr !! {this} &&
    g.Valid() && w.Valid() &&
    ready == (g.hasBeans && w.waterLevel != 0)
  }

  constructor()
    ensures Valid() && fresh(Repr)
  {
    g := new Grinder();
    w := new WaterTank();
    ready := false;
    new;
    Repr := {this, g, w} + g.Repr + w.Repr;
  }

  predicate Ready()
    requires Valid()
    reads Repr
    ensures Ready() == ready
  {
    g.Ready() && w.Level() != 0
  }

  method Restock()
    requires Valid()
    modifies Repr
    ensures Valid() && Ready() && fresh(Repr - old(Repr))
  {
    assert w.Valid();
    assert w.Repr !! g.Repr;
    assert this !in g.Repr;
    g.AddBeans();
    assert w.Valid();
    w.Fill();
    ready := true;
    Repr := Repr + g.Repr + w.Repr;
  }

  method Dispense()
    requires Valid() && Ready() && w.waterLevel != 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
  {
    g.Grind();
    w.Use();
    ready := g.hasBeans && w.waterLevel != 0;
    Repr := Repr + g.Repr + w.Repr;
  }

  method ChangeGrinder()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
  {
    g := new Grinder();
    ready := false;
    Repr := Repr + g.Repr;
  }

  method InstallCustomGrinder(grinder: Grinder)
    requires Valid() && grinder.Valid() && grinder.Repr !! Repr
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr) - grinder.Repr)
  {
    g := grinder;
    ready := (g.hasBeans && w.waterLevel > 0);
    Repr := Repr + g.Repr;
  }
}

method TestHarness() {
  var cm := new CoffeeMaker();
  cm.Restock();
  assert cm.Ready();
  cm.Dispense();
}

// Exercise10.3
class BoundedQueue<T(0)> {
  ghost var contents: seq<T>
  ghost var N: nat
  ghost var Repr: set<object>
  var data: array<T>
  var wr: nat
  var rd: nat
  var empty: bool

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |contents| <= N
  {
    this in Repr && data in Repr &&
    0 < data.Length == N && wr < N && rd < N &&
    (empty ==> rd == wr) &&
    contents == if rd < wr then data[rd..wr] else if !empty then data[rd..] + data[..wr] else [ ]
  }

  constructor (N: nat)
    requires N > 0
    ensures Valid() && fresh(Repr) && contents == [] && this.N == N
  {
    contents := [];
    this.N := N;
    data := new T[N];
    rd, wr, empty := 0, 0, true;
    Repr := {this, data};
  }

  method Insert(x: T)
    requires Valid()
    requires |contents| != N
    modifies Repr
    ensures contents == old(contents) + [x]
    ensures N == old(N)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    contents := contents + [x];
    data[wr] := x;
    if wr == data.Length - 1 {
      wr := 0;
    } else {
      wr := wr + 1;
    }
    empty := false;
  }

  method Remove() returns (x: T)
    requires Valid()
    requires |contents| != 0
    modifies Repr
    ensures contents == old(contents[1..]) && x == old(contents[0])
    ensures N ==old(N)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    contents := contents[1..];
    x := data[rd];
    if rd == data.Length - 1 {
      rd := 0;
    } else {
      rd := rd + 1;
    }
    empty := (rd == wr);
  }
}