//Q1
method Rearrange(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==>
                        (exists j :: 0 <= j < a.Length && a[j] == i) ==> a[i] == i
  ensures multiset(a[..]) == multiset(old(a[..]))                                                  // The multiset of elements remains unchanged.
  decreases *
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length                                                                   // Loop‑Technique 1: Look in the postcondition, Bound on loop variable
    invariant multiset(a[..]) == multiset(old(a[..]))                                              // Loop‑Technique 5：Use the postcondition
    invariant forall i :: 0 <= i < a.Length ==>
                            (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i                    // Loop‑Technique 3：Replace constant
    decreases *
  {
    while 0 <= a[n] < a.Length && a[n] != n && a[a[n]] != a[n]
      invariant multiset(a[..]) == multiset(old(a[..]))                                            // Loop‑Technique 5：Use the postcondition
      invariant forall i :: 0 <= i < a.Length ==>
                              (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i                 // Loop‑Technique 6：Weaken the postcondition from outer loop
      decreases *
    {
      a[n], a[a[n]] := a[a[n]], a[n];
    }
    // {invariant forall i :: 0 <= i < a.Length ==> (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i}
    // a[n] is the value observed most recently, so it cannot guarantee that a[j] == i ==> a[i] == i, so j == n needs to be excluded.
    // {invariant forall i :: 0 <= i < a.Length ==> (exists j :: (0 <= j < n && a[j] == i) || (j == n && a[j] == i)) ==> a[i] == i}
    // {invariant forall i :: 0 <= i < a.Length ==> (exists j :: 0 <= j < n + 1 && a[j] == i) ==> a[i] == i}
    n := n + 1;
    // {invariant forall i :: 0 <= i < a.Length ==> (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i}
  }
}

//Q2
method Find(a: array<int>) returns (r: int)
  modifies a
  ensures 0 <= r <= a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures r == a.Length || r !in a[..]
  ensures forall i :: 0 <= i < r ==> i in a[..]
  decreases *
{
  Rearrange(a);                               // Q1

  r := 0;
  while r < a.Length && a[r] == r
    invariant 0 <= r <= a.Length                                                                  // Loop‑Technique 5：Use the postcondition, Bound on loop variable
    invariant forall i :: 0 <= i < a.Length && i in a[..] ==> a[i] == i                           // Loop‑Technique 6：Weaken the Rearrange postcondition
    invariant forall i :: 0 <= i < r ==> i in a[..]                                               // Loop‑Technique 5：Use the postcondition
    invariant multiset(a[..]) == multiset(old(a[..]))                                             // Loop‑Technique 5：Use the postcondition
    decreases *
  {
    // {invariant forall i :: 0 <= i < r ==> i in a[..]}
    // Similarly, r as the value of the new observation may not satisfy i == r ==> i in a[..], so it cannot be included.
    // {invariant forall i :: 0 <= i < r || i == r ==> i in a[..]}
    // {invariant forall i :: 0 <= i < r + 1 ==> i in a[..]}
    r := r + 1;
    // {invariant forall i :: 0 <= i < r ==> i in a[..]}
  }
}

//Q4 - CSSE3100 students should delete this line and the following line
method FindAll(a: array<int>) returns (b: array<bool>)
  modifies a
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==>
                        ( i in multiset(a[..]) <==> b[i] )
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases *
{
  Rearrange(a);                       // Q1
  b := new bool[a.Length];
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length                                                                   // Loop‑Technique 1: Look in the postcondition, Bound on loop variable
    invariant forall i :: 0 <= i < a.Length && i in a[..] ==> a[i] == i                            // Loop‑Technique 6：Weaken the Rearrange postcondition
    invariant forall i :: 0 <= i < n ==>
                            ( i in multiset(a[..]) <==> b[i] )                                     // Loop‑Technique 3：Replace constant
    invariant multiset(a[..]) == multiset(old(a[..]))                                              // Loop‑Technique 5：Use the postcondition
    decreases *
  {
    if n == a[n] {
      b[n] := true;
    } else {
      b[n] := false;
    }
    // {forall i :: 0 <= i < n ==> ( i in multiset(a[..]) <==> b[i] )}
    // Similarly, a[n] is the value of the new observation, and it cannot guarantee that i in multiset(a[..]) <==> b[i], so it cannot be included.
    // {forall i :: 0 <= i < n + 1 ==> ( i in multiset(a[..]) <==> b[i] )}
    n := n + 1;
    // {forall i :: 0 <= i < n ==> ( i in multiset(a[..]) <==> b[i] )}
  }
}
