method Q1(A:bool,B:bool)
{
  ghost var PS: bool;
  PS := (A ==> B) && (!A ==> B);
  PS := (!A || B) && (A || B);                 // A.22
  PS := (B || !A) && (B || A);                 // A.3
  PS := B || (!A && A);                        // A.8
  PS := B || false;                            // A.15
  PS := B;                                     // A.12
}

predicate IsLeapYear(y:nat) {
  y%4 == 0 && (y%100 == 0 ==> y%400==0)
}

ghost function DaysInYear(y:nat): nat{
  if IsLeapYear(y) then 366 else 365
}

ghost function Year(d:nat, y:nat):nat {
  if d > DaysInYear(y) then Year(d-DaysInYear(y),y+1) else y
}

method CalculateYear(d: nat) returns (year: nat)
  requires d > 0
  ensures year == Year(d,1980)
{
  ghost var WP: bool;
  ghost var WP_s: bool;
  WP := d > 0;                                                                                                     // Arithmetic
  WP_s := d >= 0 && d > 0;                                                                                         // Strengthen d > 0;
  WP := d >= 0;                                                                                                    // A.9
  WP := d >= 0 && true;
  WP := d >= 0 && Year(d,1980) == Year(d,1980);
  year:= 1980;
  WP := d >= 0 && Year(d,year) == Year(d,1980);
  var days := d;
  WP := days >= 0 && Year(days,year) == Year(d,1980);
  while days > 365
    invariant days >= 0 && Year(days,year) == Year(d,1980)
  {
    WP := Year(days,year) == Year(d,1980);                                                                        // Arithmetic
    WP := ( (year%4 == 0 && (year%100 == 0 ==> year%400==0)) && ((days > 366 && days - 366 >= 0 && Year(days - 366,year+1) == Year(d,1980)) || (days <= 366 && days - 366 >= 0 && Year(days - 366,year) == Year(d,1980))) ) || (!(year%4 == 0 && (year%100 == 0 ==> year%400==0))&&days - 365 >= 0 && Year(days - 365,year + 1) == Year(d,1980));
    WP := ((year%4 == 0 && (year%100 == 0 ==> year%400==0)) ==> (days > 366 && days - 366 >= 0 && Year(days - 366,year+1) == Year(d,1980)) || (days <= 366 && days - 366 >= 0 && Year(days - 366,year) == Year(d,1980))) && (!(year%4 == 0 && (year%100 == 0 ==> year%400==0)) ==> days - 365 >= 0 && Year(days - 365,year + 1) == Year(d,1980));
    if IsLeapYear(year) {
      WP := (days > 366 && days - 366 >= 0 && Year(days - 366,year+1) == Year(d,1980)) || (days <= 366 && days - 366 >= 0 && Year(days - 366,year) == Year(d,1980));                      // A.38
      WP := (days > 366 ==> days - 366 >= 0 && Year(days - 366,year+1) == Year(d,1980)) && (days <= 366 ==> days - 366 >= 0 && Year(days - 366,year) == Year(d,1980));
      if days > 366 {
        WP := days - 366 >= 0 && Year(days - 366,year+1) == Year(d,1980);
        days := days - 366;
        WP := days >= 0 && Year(days,year+1) == Year(d,1980);
        year := year+1;
        WP := days >= 0 && Year(days,year) == Year(d,1980);
      } else {
        WP := days - 366 >= 0 && Year(days - 366,year) == Year(d,1980);
        days := days - 366;
        WP := days >= 0 && Year(days,year) == Year(d,1980);
      }
      WP := days >= 0 && Year(days,year) == Year(d,1980);
    } else {
      WP := days - 365 >= 0 && Year(days - 365,year + 1) == Year(d,1980);
      days := days - 365;
      WP := days >= 0 && Year(days,year + 1) == Year(d,1980);
      year:= year + 1;
      WP := days >= 0 && Year(days,year) == Year(d,1980);
    }
    WP := days >= 0 && Year(days,year) == Year(d,1980);
  }
  WP_s := days >= 0 && Year(days,year) == Year(d,1980) && days <= 365;                                             // Strengthen days <= 365
  WP := year == Year(d,1980);
}

method Q3(d: nat) returns (year: nat)
  requires d > 0
  ensures year == Year(d,1980)
{
  year:= 1980;
  var days := d;
  while days > 365
    invariant days >= 0 && Year(days,year) == Year(d,1980)
    decreases days
  {
    ghost var WP: bool;
    ghost var WP_s: bool;
    /*
    The method terminates since days >= 0 is implied by the invariant.
    */
    WP := days >= 0;                                                                                                          // Use Q1
    WP := (IsLeapYear(year) ==> days >= 0) && (!IsLeapYear(year) ==> days >= 0);                                              // A.2 A.9
    WP := (IsLeapYear(year) ==> true && days >= 0) && (!IsLeapYear(year) ==> true && days >= 0);                              // Arithmetic
    WP := (IsLeapYear(year) ==> days > days - 366 && days >= 0) && (!IsLeapYear(year) ==> days > days - 365 && days >= 0);
    ghost var m := days;
    WP := (IsLeapYear(year) ==> m > days - 366 && m >= 0) && (!IsLeapYear(year) ==> m > days - 365 && m >= 0);
    if IsLeapYear(year) {
      WP := m > days - 366 && m >= 0;                                              // use Q1;
      WP := (days > 366 ==> m > days - 366 && m >= 0) && (days <= 366 ==> m > days - 366 && m >= 0);
      if days > 366 {
        WP := m > days - 366 && m >= 0;
        days := days - 366;
        WP := m > days && m >= 0;
        year := year+1;
        WP := m > days && m >= 0;                          // m ≻ days
      } else {
        WP := m > days - 366 && m >= 0;
        days := days - 366;
        WP := m > days && m >= 0;                          // m ≻ days
      }
      WP := m > days && m >= 0;                          // m ≻ days
    } else {
      WP := m > days - 365 && m >= 0;
      days := days - 365;
      WP := m > days && m >= 0;
      year:= year + 1;
      WP := m > days && m >= 0;                          // m ≻ days
    }
    WP := m > days && m >= 0;                          // m ≻ days
  }
}