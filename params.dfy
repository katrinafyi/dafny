function Power(k: nat): nat {
if k == 0 then 1 else 2 * Power(k - 1)
}
method DivMod(a: int, b: int) returns (q: int, r: int)
 requires a >= 0 && b > 0
 ensures a == q*b + r && 0 <= r < b
{
 var c := b;
 var k := 0;
 while c <= a
 invariant k >= 0 && c == Power(k)*b && a >= 0
 {
 c, k := 2*c, k + 1;
 }
 q, r := 0, a;
 while c != b 
 invariant k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c
 {
 q, c, k := q*2, c/2, k - 1;
 if r >= c {
 q, r := q + 1, r - c;
 }
 }
}
