function Power(k: nat): nat {
  if k == 0 then 1 else 2 * Power(k - 1)
}

lemma {:axiom} Distrib(a: int, b: int, factor: int)
  ensures (a+b)*factor == a*factor + b*factor
{
}

predicate DivModRel(dividend: int, divisor: int, q: int, r: int)
{
  dividend == q*divisor + r && 0 <= r < divisor
}

/**
 * A division algorithm using only linear arithmetic and bitwise operations.
 */
method DivMod(a: int, b: int) returns (q: int, r: int)
  requires a >= 0 && b > 0
  ensures DivModRel(a,b,q,r)
{
  assert (b == Power(0)*b && a >= 0);
  var c := b;
  assert (0 >= 0 && c == Power(0)*b && a >= 0);
  var k := 0;
  assert (k >= 0 && c == Power(k)*b && a >= 0);

  // c is multiplied by 2 until it exceeds our dividend.
  while c <= a
    invariant k >= 0 && c == Power(k)*b && a >= 0
  {
    assert (k+1 >= 0 && 2*c == Power(k+1)*b && a >= 0);
    c, k := 2*c, k + 1;
    assert (k >= 0 && c == Power(k)*b && a >= 0);
  }
  assert (c > a && (k >= 0 && c == Power(k)*b && a >= 0));
  // now, c is greater than a, and is a multiple of 2 and our divisor.

  assert (k >= 0 && c == Power(k)*b && DivModRel(a,c,0,a));
  q, r := 0, a;
  // initialise quotient to 0 and remainder to a.

  assert (k >= 0 && c == Power(k)*b && DivModRel(a,c,q,r));
  while c != b
    invariant k >= 0 && c == Power(k)*b && DivModRel(a,c,q,r)
    decreases k
  {
    assert k >= 1;
    assert even: c % 2 == 0 by {
      assert c == Power(k-1)*b + Power(k-1)*b;
    }

    calc {
      (k >= 1 && c == Power(k)*b && DivModRel(a,c,q,r));
      == { reveal even; }
      (k-1 >= 0 && c/2 == Power(k-1)*b && a == (q*2)*(c/2)+r && 0 <= r < c);
    }
    q, c, k := q*2, c/2, k - 1;
    assert (k >= 0 && c == Power(k)*b && a == q*c+r && 0 <= r < c+c);

    assert (
      (r >= c ==> k >= 0 && c == Power(k)*b && a == q*c + r && r < c+c)
      && 
      (r < c  ==> k >= 0 && c == Power(k)*b && a == q*c+r && 0 <= r)
    );

    assert (
      if r >= c 
      then (k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r-c < c)
      else (k >= 0 && c == Power(k)*b && DivModRel(a,c,q,r)));

    if r >= c {
      calc {
        (k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r-c < c);
        ==
        (k >= 0 && c == Power(k)*b && a == ((q)*c + c) + (r-c) && 0 <= r-c < c);
        ==
        (k >= 0 && c == Power(k)*b && DivModRel(a,c,q+1,r-c));
      }
      q, r := q + 1, r - c;
      assert (k >= 0 && c == Power(k)*b && DivModRel(a,c,q,r));
    }
    assert (k >= 0 && c == Power(k)*b && DivModRel(a,c,q,r));
  }
  calc {
    c == b && (k >= 0 && c == Power(k)*b && DivModRel(a,c,q,r)); 
    ==
    DivModRel(a,b,q,r);
  }
}
