ghost function Count(lo: nat, hi: nat, s:seq<int>):int
  requires lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0
  else if s[hi-1]%2 == 0 then 1 + Count(lo, hi-1, s) else Count(lo, hi-1, s)
}

method PreCompute(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  requires a != b
  modifies b

  ensures forall i :: 0 <= i < b.Length ==> b[i] == Count(0,i+1,a[..])
{
  ComputeCount(a,b,0);
}

method ComputeCount(a: array<int>, b: array<int>, n: nat)
  requires a.Length == b.Length
  requires a != b
  modifies b

  requires n <= a.Length
  decreases a.Length - n

  requires forall i :: 0 <= i < n ==> b[i] == Count(0,i+1,a[..])
  ensures forall i :: 0 <= i < a.Length ==> b[i] == Count(0,i+1,a[..])
{
  if n == a.Length {
    return;
  }
  var d := 1 - a[n] % 2;
  b[n] := d + (if n == 0 then 0 else b[n-1]);
  ComputeCount(a, b, n+1);
}

lemma CountOfSlice(lo: nat, hi: nat, s: seq<int>)
  requires lo <= hi <= |s|
  ensures Count(lo,hi,s) == Count(0,hi,s) - Count(0,lo,s)
{}

method Evens(a: array<int>) returns (c: array2<int>)
  ensures fresh(c)
  ensures a.Length == c.Length0 == c.Length1
  ensures forall i,j :: 0 <= i <= j < a.Length ==>
                          c[i,j] == Count(i,j+1,a[..])

{
  c := new int[a.Length,a.Length];

  var b := new int[a.Length];
  PreCompute(a,b);

  for ii := 0 to a.Length
    invariant forall i :: 0 <= i < b.Length ==> b[i] == Count(0,i+1,a[..])
    invariant forall i,j :: 0 <= i <= j < a.Length && i < ii ==> c[i,j] == Count(i,j+1,a[..])
  {
    for jj := ii to a.Length
      invariant forall i :: 0 <= i < b.Length ==> b[i] == Count(0,i+1,a[..])
      invariant forall i,j :: 0 <= i <= j < a.Length && i < ii ==> c[i,j] == Count(i,j+1,a[..])
      invariant forall i,j :: 0 <= i <= j < jj && i == ii ==> c[i,j] == Count(i,j+1,a[..])
    {
      CountOfSlice(ii,jj+1,a[..]); 
      c[ii,jj] := b[jj] - if ii > 0 then b[ii-1] else 0;
    }
  }
}

method PreComputeLoop(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  requires a != b
  modifies b

  ensures forall i :: 0 <= i < b.Length ==> b[i] == Count(0,i+1,a[..])
{
  for n := 0 to a.Length
    invariant forall i :: 0 <= i < n ==> b[i] == Count(0,i+1,a[..])
  {
    var d := 1 - a[n] % 2;
    b[n] := d + (if n == 0 then 0 else b[n-1]);
  }
}
