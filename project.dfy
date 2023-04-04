function Project<T(==)>(xs: seq<T>, key: T): seq<T>
{
  if xs == [] then [] 
  else if xs[0] == key then [key] + Project(xs[1..],key)
  else Project(xs[1..],key)
}

lemma MultisetMultiplicity<T>(ms: seq<T>, x: T)
requires ms != []
requires ms[0] != x
ensures multiset(ms)[x] == multiset(ms[1..])[x]
{
  assert ms == [ms[0]] + ms[1..];
}

// lemma ProjectHomo<T>(xs: seq<T>, ys: seq<T>, key: T)
//   ensures Project(xs+ys,key) == Project(xs,key) + Project(ys,key)
// {
//   if xs == [] {
//     assert xs+ys == ys;
//   } else if ys == [] {
//     assert xs+ys == xs;
//   } else {

//   }
// }

lemma SeqAppendFront<T>(front: seq<T>, xs: seq<T>, ys: seq<T>)
  requires front + xs == front + ys 
  ensures xs == ys
{
  if xs == [] {}
  else if ys == [] {}
  else if |xs| != |ys| {}
  else if xs != ys {
    var i :| 0 <= i < |xs| && xs[i] != ys[i];
    assert (front + xs)[i+|front|] == xs[i]; 
  }
}

lemma ProjectCardinality<T>(xs: seq<T>, key: T)
  ensures |Project(xs,key)| == multiset(xs)[key] 
{
  if xs == [] {}
  else if xs[0] != key {
    assert Project(xs,key) == Project(xs[1..],key);
    assert xs == [xs[0]] + xs[1..];
    assert multiset(xs)[key] == multiset(xs[1..])[key];
    ProjectCardinality(xs[1..], key);
  }
}


lemma ProjectCardinalityEqual<T>(xs: seq<T>, ys: seq<T>, key: T)
  requires |Project(xs,key)| == |Project(ys,key)|
  ensures multiset(xs)[key] == multiset(ys)[key]
{
  ProjectCardinality(xs,key);
  ProjectCardinality(ys,key);
}

lemma ProjectToMultiset<T>(xs: seq<T>, ys: seq<T>)
  requires forall x :: x in xs || x in ys ==> |Project(xs,x)| == |Project(ys,x)|
  ensures multiset(xs) == multiset(ys)
  decreases |ys| < |xs|
{
  if xs == [] {
    if ys != [] {
      assert Project(ys,ys[0]) != [];
    }
  } else if ys == [] {
    ProjectToMultiset(ys,xs);
  } else if multiset(xs) != multiset(ys) {
    var diff :| multiset(xs)[diff] != multiset(ys)[diff];
    ProjectCardinality(xs,diff);
    ProjectCardinality(ys,diff);
  }
}

lemma MultisetToProject<T>(xs: seq<T>, ys: seq<T>)
  requires multiset(xs) == multiset(ys)
  ensures forall x :: x in xs || x in ys ==> |Project(xs,x)| == |Project(ys,x)|
{
  if xs == [] {} 
  else if ys == [] {}
  else {
    forall x | x in xs || x in ys
      ensures |Project(xs,x)| == |Project(ys,x)|
    {
      assert multiset(xs)[x] == multiset(ys)[x];
      ProjectCardinality(xs,x);
      ProjectCardinality(ys,x);
    }
  }
}

lemma MultisetCardinalityEqual<T>(xs: seq<T>, ys: seq<T>)
  requires |multiset(xs)| == |multiset(ys)|
  ensures |xs| == |ys| 
{}

lemma StableImpliesUnstable<T>(xs: seq<T>, ys: seq<T>)
  requires forall x :: x in xs || x in ys ==> Project(xs,x) == Project(ys,x)
  ensures forall x :: x in xs || x in ys ==> |Project(xs,x)| == |Project(ys,x)|
{}
