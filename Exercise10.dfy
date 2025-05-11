class UniqueNumberAllocator {
  ghost var used: set<nat>
  ghost predicate Valid( )
    reads this
  constructor ( )
    ensures Valid( ) && used == {}
  method Allocate( ) returns (n: nat)
    requires Valid( )
    modifies this
    ensures Valid( ) && n !in old(used) && used == old(used) + {n}
  method Reset( )
    requires Valid( )
    modifies this
    ensures Valid( ) && used == {}
}