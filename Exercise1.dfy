// exercise1.1
method MaxSum(x: int, y: int) returns (s: int, m: int)
  requires true
  ensures s == x + y
  ensures (x <= y && m == y ) || (x > y && m == x)
{
  s := x + y;
  if (x >= y){
    m := x;
  } else {
    m := y;
  }
}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2*m // 
  ensures s == x + y && ((x <= y && m == y) || (x > y && m == x))
{
  x := m;
  y := s - m;
}

// exercise1.2
function F(): int {
  29
}

method M() returns (r: int)
  ensures r == 29 // 
{
  r := 29;
}

method Caller() returns (a: int, b: int)
  ensures a == 29
  ensures b == 29  // failed because not specifed for method
{
  a := F();
  b := M();
}

method Index(n: int) returns (i: int)
  requires n >= 1
  ensures i == n/2 //
{
  i := n/2;
}

method IndexCaller() returns (x: int, y: int)
  ensures x == y  // this postcondition is not satisfied
{
  x := Index(50);
  y := Index(50);
}

// exercise 1.3
// Prove the following using only De Morgan's Law: !(X || Y)  =  !X && !Y  and laws of ! and &&.

// a)  X || true     ==    true 
// X || true  ==  !!(x || true)       [rule A.17]
//            ==  !(A || B) ==





// b)  X || X    ==    X 
// X || X  ==  

// c)  X || Y    ==    Y || X


// Exercise 1.5

// d) X || Y ==> Z    ==    (X ==> Z) && (Y ==> Z)
//    X || Y ==> Z  == !(X || Y) || Z           [rule A.22]
//                  == (!X && !Y) || Z          [rule A.19]
//                  == Z || (!X && !Y)          [rule A.3]
//                  == (Z || !X) && (Z || !Y)   [rule A.8]
//                  == (!X || Z) && (!Y || Z)   [rule A.3]
//                  == (X ==> Z) && (Y ==> Z)   [rule A.22]


// Exercise 1.6
// a)   (P && Q ==> R) && !R && P   ==>  !Q
// (P && Q ==> R) && !R && P  == (!(P && Q) || R) && !R && P              [rule A.22]
//                            == (!P && !Q || R) && !R && P               [rule A.18]
//                            == 


// b)   (x < 5 ==> y == 10) && y < 7 && (y < 1000 ==> x <= 5)   ==>   x == 5
// 