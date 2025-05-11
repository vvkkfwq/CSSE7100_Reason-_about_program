method Min(a: array<int>) returns (m: int) 
	requires a.Length > 0
	ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
	ensures exists i :: 0 <= i < a.Length && m == a[i]
{
	var n := 0;
	m := a[0];
	while n != a.Length
		invariant 0 <= n <= a.Length
		invariant forall i :: 0 <= i < n ==> m <= a[i]	
		// replace a constant by a variable
		invariant exists i :: 0 <= i < a.Length && m == a[i]
		// use postcondition
	{
		if a[n] < m {
			m := a[n];
		}
		n := n +1;
	}
}





method Test(a: array<int>) returns (m: int)
	requires a.Length == 3 && a[0] == 1 && a[1] == 2 && a[2] == 0
	ensures m == 0
{
	m := Min(a);
}