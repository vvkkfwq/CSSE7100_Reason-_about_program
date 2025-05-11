method Rearrange(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==>
                        (exists j :: 0 <= j < a.Length && a[j] == i) ==> a[i] == i
  ensures multiset(a[..]) == multiset(old(a[..]))                // The multiset of elements remains unchanged.
  decreases *
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length                                 // bounds
    invariant multiset(a[..]) == multiset(old(a[..]))            // Loop‑Technique 5：Use the postcondition
    invariant forall i :: 0 <= i < a.Length ==>
                            (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i                    // Loop‑Technique 3：Replace constant
    decreases *
  {
    while 0 <= a[n] < a.Length && a[n] != n && a[a[n]] != a[n]
      invariant 0 <= n < a.Length                                  // bounds
      invariant multiset(a[..]) == multiset(old(a[..]))            // Loop‑Technique 5：Use the postcondition
      invariant forall i :: 0 <= i < a.Length ==>
                              (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i                 // Loop‑Technique 3：Replace constant
      decreases *
    {
      a[n], a[a[n]] := a[a[n]], a[n];
    }
    n := n + 1;
  }
}

method FindAll(a: array<int>) returns (b: array<bool>)
  requires a != null
  modifies a
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length && i in a[..]  ==>  b[i]
  ensures forall i :: 0 <= i < a.Length && i !in a[..] ==> !b[i]

  // ensures forall i :: 0 <= i < a.Length ==>
  //                       ( i in multiset(a[..]) <==> b[i] )
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases *
{
  Rearrange(a);                       // Q1
  b := new bool[a.Length];
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant b.Length == a.Length
    invariant forall i :: 0 <= i < a.Length && i in a[..] ==> a[i] == i
    invariant forall i :: 0 <= i < n && i in a[..]  ==>  b[i]
    invariant forall i :: 0 <= i < n && i !in a[..] ==> !b[i]

    // invariant forall i :: 0 <= i < n ==>
    //                         ( i in multiset(a[..]) <==> b[i] )
    invariant multiset(a[..]) == multiset(old(a[..]))      // LT‑5
    decreases *
  {
    if n == a[n]{
      b[n] := true;
    }else {
      b[n] := false;
    }
    n := n + 1;
  }
}