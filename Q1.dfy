// Q1
method Rearrange(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==>
                        (exists j :: 0 <= j < a.Length && a[j] == i) ==> a[i] == i
  // ensures forall i :: 0 <= i < a.Length ==> (i !in multiset(old(a[..])) ==> a[i] != i)
  ensures multiset(a[..]) == multiset(old(a[..]))                // The multiset of elements remains unchanged.
  decreases *
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length                                 // bounds
    invariant multiset(a[..]) == multiset(old(a[..]))            // Loop‑Technique 5：Use the postcondition
    invariant forall i :: 0 <= i < a.Length ==>
                            (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i                    // Loop‑Technique 3：Replace constant
    // invariant forall i :: 0 <= i <  n ==> (i !in multiset(old(a[..])) ==> a[i] != i)
    decreases *
  {
    while 0 <= a[n] < a.Length && a[n] != n && a[a[n]] != a[n]
      // invariant 0 <= n < a.Length                                  // bounds
      invariant multiset(a[..]) == multiset(old(a[..]))            // Loop‑Technique 5：Use the postcondition
      invariant forall i :: 0 <= i < a.Length ==>
                              (exists j :: 0 <= j < n && a[j] == i) ==> a[i] == i                 // Loop‑Technique 3：Replace constant
      // invariant forall i :: 0 <= i < n ==> (i !in multiset(old(a[..])) ==> a[i] != i)
      decreases *
    {
      a[n], a[a[n]] := a[a[n]], a[n];
    }
    n := n + 1;
  }
}

// Task sheet. All swaps occur while n == 0.
method TestRearrange1(a: array<int>)
  requires a.Length == 6
  requires a[0] == 2 && a[1] == -3 && a[2] == 4 && a[3] == 1 && a[4] == 1 && a[5] == 7
  ensures a[1] == 1 && a[2] == 2 && a[4] == 4

  decreases *
  modifies a
{
  assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
  Rearrange(a);
}

// One swap at n == 0, n == 2 (and block as a[1] == 1]), n == 3
method TestRearrange2(a: array<int>)
  requires a.Length == 6
  requires a[0] == 1 && a[1] == -3 && a[2] == 4 && a[3] == 2 && a[4] == 1 && a[5] == 7
  ensures a[1] == 1 && a[2] == 2 && a[4] == 4

  decreases *
  modifies a
{
  assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
  Rearrange(a);
}

// I don't know why this wouldn't work but the empty list is always an edge case so
method TestRearrange3(a: array<int>)

  requires a.Length == 0
  ensures a.Length == 0

  decreases *
  modifies a
{
  assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
  Rearrange(a);
}

// All swap, all swaps occur at n == 0
method TestRearrange4(a: array<int>)
  requires a.Length == 6
  requires a[0] == 2 && a[1] == 4 && a[2] == 0 && a[3] == 1 && a[4] == 3 && a[5] == 5
  ensures a[0] == 0 && a[1] == 1 && a[2] == 2 && a[3] == 3 && a[4] == 4 && a[5] == 5

  decreases *
  modifies a
{
  assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
  Rearrange(a);
}

// Nothing happens
method TestRearrange5(a: array<int>)
  requires a.Length == 6
  requires a[0] == -3 && a[1] == 1 && a[2] == 2 && a[3] == 1 && a[4] == 4 && a[5] == 7
  ensures a[1] == 1 && a[2] == 2 && a[4] == 4

  decreases *
  modifies a
{
  assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
  Rearrange(a);
}

// ============ 通用的检查谓词 ============

// “Rearrange” 语义：对原序列 s、排好序的数组 a 进行检查
predicate RearrangeOK(a: array<int>, s: seq<int>)
  reads a
{
  // 1) 多重集保持
  multiset(a[..]) == multiset(s) &&
  // 2) 若 i 在原序列中出现过，则排完后 a[i] == i
  forall i :: 0 <= i < |s| ==>
                (i in multiset(s)) ==> a[i] == i
}

// ============ 测试用例 1：完全可对齐 ============
// a[i] == i 对所有 i 都能成立
method Test_Rearrange_AllMatch(a:array<int>)
  modifies a
  decreases *
{
  var a := new int[5][0,1,2,3,4];
  var oldSeq := a[..];        // 保存原序列
  Rearrange(a);
  assert RearrangeOK(a, oldSeq);
}

// ============ 测试用例 2：一个都不能对齐 ============
// 原数组里没有 0..4 中的任何值
method Test_Rearrange_NoneMatch(a:array<int>)
  modifies a
  decreases *
{
  var a := new int[5][-5,-4,-3,-2,-1];
  var oldSeq := a[..];
  Rearrange(a);
  assert RearrangeOK(a, oldSeq);
}

// ============ 测试用例 3：部分可对齐、含重复值 ============
// 0 和 3 各出现一次，1、2 缺失；4 重复出现三次
method Test_Rearrange_PartialWithDuplicates(a:array<int>)
  modifies a
  decreases *
{
  var a := new int[6][4,3,4,0,4,10];
  var oldSeq := a[..];
  Rearrange(a);
  assert RearrangeOK(a, oldSeq);
}

// ============ 测试用例 4：含负数与越界的大数 ============
// -1、8 等应被忽略，1 出现两次
method Test_Rearrange_NegativeAndLarge(a:array<int>)
  modifies a
  decreases *
{
  var a := new int[8][-1,1,99,7,1,8,3,2];
  var oldSeq := a[..];
  Rearrange(a);
  assert RearrangeOK(a, oldSeq);
}

// ============ 测试用例 5：数组中有 0，但 0 在错误位置 ============
// 检查内部 swap 循环能把 0 放到 a[0]
method Test_Rearrange_MisplacedZero(a:array<int>)
  modifies a
  decreases *
{
  var a := new int[4][2,0,3,1];
  var oldSeq := a[..];
  Rearrange(a);
  assert RearrangeOK(a, oldSeq);
}

// ============ 测试用例 6：长度为 1 的极端情况 ============
// a[0] == 0   —— 必须保持； a[0] == 5 —— 随意
method Test_Rearrange_Length1(a:array<int>)
  modifies a
  decreases *
{
  var a1 := new int[1][0];
  var s1 := a1[..];
  Rearrange(a1);
  assert RearrangeOK(a1, s1);

  var a2 := new int[1][5];
  var s2 := a2[..];
  Rearrange(a2);
  assert RearrangeOK(a2, s2);
}


method test(a:array<int>)
  requires a.Length == 6
  requires a[0] == 2 && a[1] == -3 && a[2] == 4 && a[3] == 1 && a[4] == 1 && a[5] == 7
  modifies a
  ensures a[1] == 1 && a[2] == 2 && a[4] == 4
  decreases *
{
  assert forall i :: i in a[..] <==> i in multiset(a[..]);
  assert 1 in a[..];
  assert 2 in a[..];
  assert 4 in a[..];
  Rearrange(a);
  assert 1 in a[..];
  assert 2 in a[..];
  assert 4 in a[..];
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
  Rearrange(a);

  r := 0;
  while r < a.Length && a[r] == r
    invariant 0 <= r <= a.Length
    // invariant forall i :: 0 <= i < r && i in a[..] ==> a[i] == i
    invariant forall i :: 0 <= i < r ==> i in a[..]
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases *
  {
    r := r + 1;
  }
}

// (task sheet) Missing a 0
method TestFind1(a: array<int>) returns (r: int)
  requires a.Length == 6
  requires a[0] == 2 && a[1] == -3 && a[2] == 4 && a[3] == 1 && a[4] == 1 && a[5] == 7
  ensures r == 0

  decreases *
  modifies a
{
  assert 0 !in a[..];
  assert forall i :: i in a[..] <==> i in multiset(a[..]);
  r := Find(a);
}

// Has numbers [0, 1, 2] and 4 but not 3
method TestFind2(a: array<int>) returns (r: int)
  requires a.Length == 6
  requires a[0] == 2 && a[1] == 0 && a[2] == 4 && a[3] == 1 && a[4] == 1 && a[5] == 7
  ensures r == 3

  decreases *
  modifies a
{
  assert 3 !in a[..] && 5 !in a[..]; // should also work with just assert 3 !in a[..]
  assert forall i :: i in a[..] <==> i in multiset(a[..]);
  r := Find(a);
}

// All numbers accounted for
method TestFind3(a: array<int>) returns (r: int)
  requires a.Length == 6
  requires a[0] == 2 && a[1] == 4 && a[2] == 0 && a[3] == 1 && a[4] == 3 && a[5] == 5
  ensures r == 6

  decreases *
  modifies a
{
  assert forall i :: i in a[..] <==> i in multiset(a[..]);
  r := Find(a);
}

// Empty List
method TestFind4(a: array<int>) returns (r: int)
  requires a.Length == 0
  ensures r == 0

  decreases *
  modifies a
{
  r := Find(a);
}

// One element (0)
method TestFind5(a: array<int>) returns (r: int)
  requires a.Length == 1
  requires a[0] == 0
  ensures r == 1

  decreases *
  modifies a
{
  assert a[0] == 0;
  assert 0 in a[..];
  assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
  assert forall i :: 0 <= i < a.Length ==> a[i] in multiset(old(a[..]));
  r := Find(a);
  // (There's a lot of assert statements here as I was trying to get at least
  // this very simple test to work where there were some bugs in my postconditions)
}

// ---------- 规格辅助谓词（可放在文件顶部一次声明） ----------
predicate FindSpec(oldA: seq<int>, r: int)
{
  0 <= r <= |oldA| &&
  (r < |oldA| ==>
     (forall i :: 0 <= i <= r ==> i in multiset(oldA)) &&
     !(r in multiset(oldA))) &&
  (r == |oldA| ==>
     forall i :: 0 <= i < |oldA| ==> i in multiset(oldA))
}


// ===================================================================
// 用例 1：缺少 0  -----------------------------------------------------
// 用例 1：缺失 0（最小值）
method TestFind_Missing0(a: array<int>)
  requires a.Length == 4
  requires a[0] == 2 && a[1] == 3 && a[2] == 1 && a[3] == 2
  modifies a
  decreases *
{
  var oldSeq := a[..];
  var r := Find(a);
  assert r == 0;
  assert multiset(a[..]) == multiset(oldSeq);
  assert FindSpec(oldSeq, r);
}

// 用例 2：缺失中间值（缺失 2）
method TestFind_Missing2(a: array<int>)
  requires a.Length == 5
  requires a[0] == 0 && a[1] == 1 && a[2] == 3 && a[3] == 4 && a[4] == 1
  modifies a
  decreases *
{
  var oldSeq := a[..];
  var r := Find(a);
  assert r == 2;
  assert multiset(a[..]) == multiset(oldSeq);
  assert FindSpec(oldSeq, r);
}

// 用例 3：缺失最后一个值（缺失 4）
method TestFind_MissingLast(a: array<int>)
  requires a.Length == 5
  requires a[0] == 0 && a[1] == 1 && a[2] == 2 && a[3] == 3 && a[4] == 2
  modifies a
  decreases *
{
  var oldSeq := a[..];
  var r := Find(a);
  assert r == 4;
  assert multiset(a[..]) == multiset(oldSeq);
  assert FindSpec(oldSeq, r);
}

// 用例 4：无缺失（完整 0..4）
method TestFind_NoMissing(a: array<int>)
  requires a.Length == 5
  requires a[0] == 3 && a[1] == 0 && a[2] == 1 && a[3] == 4 && a[4] == 2
  modifies a
  decreases *
{
  var oldSeq := a[..];
  var r := Find(a);
  assert r == a.Length;
  assert multiset(a[..]) == multiset(oldSeq);
  assert FindSpec(oldSeq, r);
}

// 用例 5：有重复元素、缺失 0
method TestFind_Missing0WithDuplicates(a: array<int>)
  requires a.Length == 6
  requires a[0] == 1 && a[1] == 2 && a[2] == 2 && a[3] == 3 && a[4] == 4 && a[5] == 5
  modifies a
  decreases *
{
  var oldSeq := a[..];
  var r := Find(a);
  assert r == 0;
  assert multiset(a[..]) == multiset(oldSeq);
  assert FindSpec(oldSeq, r);
}



// (task sheet) Missing a 0
// method TestFind1(a: array<int>) returns (r: int)
//   requires a.Length == 6
//   requires a[0] == 2 && a[1] == -3 && a[2] == 4 && a[3] == 1 && a[4] == 1 && a[5] == 7
//   ensures r == 0

//   decreases *
//   modifies a
// {
//   assert 0 !in a[..];
//   assert forall i :: i in a[..] <==> i in multiset(a[..]);
//   r := Find(a);
// }

// // Has numbers [0, 1, 2] and 4 but not 3
// method TestFind2(a: array<int>) returns (r: int)
//   requires a.Length == 6
//   requires a[0] == 2 && a[1] == 0 && a[2] == 4 && a[3] == 1 && a[4] == 1 && a[5] == 7
//   ensures r == 3

//   decreases *
//   modifies a
// {
//   assert 3 !in a[..] && 5 !in a[..]; // should also work with just assert 3 !in a[..]
//   assert forall i :: i in a[..] <==> i in multiset(a[..]);
//   r := Find(a);
// }

// // All numbers accounted for
// method TestFind3(a: array<int>) returns (r: int)
//   requires a.Length == 6
//   requires a[0] == 2 && a[1] == 4 && a[2] == 0 && a[3] == 1 && a[4] == 3 && a[5] == 5
//   ensures r == 6

//   decreases *
//   modifies a
// {
//   assert forall i :: i in a[..] <==> i in multiset(a[..]);
//   r := Find(a);
// }

// // Empty List
// method TestFind4(a: array<int>) returns (r: int)
//   requires a.Length == 0
//   ensures r == 0

//   decreases *
//   modifies a
// {
//   r := Find(a);
// }

// // One element (0)
// method TestFind5(a: array<int>) returns (r: int)
//   requires a.Length == 1
//   requires a[0] == 0
//   ensures r == 1

//   decreases *
//   modifies a
// {
//   assert a[0] == 0;
//   assert 0 in a[..];
//   assert forall i :: 0 <= i < a.Length ==> old(a[i]) in multiset(a[..]);
//   assert forall i :: 0 <= i < a.Length ==> a[i] in multiset(old(a[..]));
//   r := Find(a);
//   // (There's a lot of assert statements here as I was trying to get at least
//   // this very simple test to work where there were some bugs in my postconditions)
// }

//Q4
method FindAll(a: array<int>) returns (b: array<bool>)
  // requires a != null
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
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < a.Length && i in a[..] ==> a[i] == i
    invariant forall i :: 0 <= i < n ==>
                            ( i in multiset(a[..]) <==> b[i] )
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases *
  {
    if n == a[n] {
      b[n] := true;
    } else {
      b[n] := false;
    }
    n := n + 1;
  }
}

predicate FindAllOK(a: array<int>, oldData: seq<int>, b: array<bool>)
  reads a, b
{
  // ① 长度保持
  b.Length == |oldData| &&
  // ② 语义：出现⇔true  未出现⇔false
  forall i :: 0 <= i < |oldData| ==>
                (b[i] <==> i in multiset(oldData)) &&
                // ③ 并未增删元素，只调换
                multiset(a[..]) == multiset(oldData)
}

// ---------- 用例 1：完全包含 0..n‑1 ----------
method Test_FindAll_AllPresent(a: array<int>)
  modifies a
  decreases *
{
  var a := new int[5][0,1,2,3,4];
  var oldSeq := a[..];
  var b := FindAll(a);
  assert FindAllOK(a, oldSeq, b);
}

// ---------- 用例 2：全缺失 ----------
method Test_FindAll_NonePresent(a: array<int>)
  modifies a
  decreases *
{
  var a := new int[5][-5,-4,-3,-2,-1];
  var oldSeq := a[..];
  var b := FindAll(a);
  assert FindAllOK(a, oldSeq, b);
}

// ---------- 用例 3：部分出现 + 重复 ----------
method Test_FindAll_PartialDuplicate(a: array<int>)
  modifies a
  decreases *
{
  var a := new int[7][4,1,4,10,2,1,99];
  var oldSeq := a[..];
  var b := FindAll(a);
  assert FindAllOK(a, oldSeq, b);
}

// ---------- 用例 4：负数 & 大数混入 ----------
method Test_FindAll_NegativeAndLarge(a: array<int>)
  modifies a
  decreases *
{
  var a := new int[6][-1,3,8,0,42,3];
  var oldSeq := a[..];
  var b := FindAll(a);
  assert FindAllOK(a, oldSeq, b);
}

// ---------- 用例 5：长度为 1 ----------
method Test_FindAll_Length1(a: array<int>)
  modifies a
  decreases *
{
  // 5a. 元素就是索引 0
  var a1 := new int[1][0];
  var s1 := a1[..];
  var b1 := FindAll(a1);
  assert FindAllOK(a1, s1, b1);

  // 5b. 元素不是索引 0
  var a2 := new int[1][7];
  var s2 := a2[..];
  var b2 := FindAll(a2);
  assert FindAllOK(a2, s2, b2);
}

// ---------- 用例 6：需要多次 swap ----------
method Test_FindAll_SwapsNeeded(a: array<int>)
  modifies a
  decreases *
{
  var a := new int[6][2,5,2,3,0,4];
  var oldSeq := a[..];
  var b := FindAll(a);
  assert FindAllOK(a, oldSeq, b);
}
