datatype L = Low | High

predicate method leq(l1:L,l2:L) {
    (l1 == Low || l2 == High)
}

// upper bound on l1 and l2
function method join(l1:L,l2:L):L {
    if leq(l1,l2) then l2 else l1
}
// lower bound on l1 and l2
function method meet(l1:L,l2:L):L {
    if leq(l1,l2) then l1 else l2
}

lemma partialorder(l1:L,l2:L,l3:L)
ensures leq(l1,l1) // reflexivity
ensures leq(l1,l2) && leq(l2,l1) ==> l1 == l2 // antisymmetry
ensures leq(l1,l2) && leq(l2,l3) ==> leq(l1,l3) // transitivity
{}

lemma joinLemma(l1:L,l2:L,l3:L)
ensures leq(l1,join(l1,l2)) && leq(l2,join(l1,l2))
ensures leq(l1,l3) && leq(l2,l3) ==> leq(join(l1,l2),l3)
ensures join(l1,l2) == join(l2,l1)
{}

lemma meetLemma(l1:L,l2:L,l3:L)
ensures leq(meet(l1,l2),l1) && leq(meet(l1,l2),l2)
ensures leq(l3,l1) && leq(l3,l2) ==> leq(l3,meet(l1,l2))
ensures meet(l1,l2) == meet(l2,l1)
{}


datatype Frame<T> = Frame(x: T, z: T, secret: T)
datatype Val<L, T> = V(v: T, gamma: L)
type Vars = Frame<Val<L, int>> // mapping of variable to their values.

function method lift<T>(v1: Val<L,T>, v2: Val<L,T>, f: (T,T) --> T): Val<L,T>
    requires f.requires(v1.v, v2.v)
    ensures leq(v1.gamma,lift(v1,v2,f).gamma)
    ensures leq(v2.gamma,lift(v1,v2,f).gamma)
{
    V(f(v1.v, v2.v), join(v1.gamma, v2.gamma))
}

function method pure<T>(t: T): Val<L,T>
{
    V(t,Low)
}



type V = Val<L,int>
class SeqLock {
    var Vars: seq<V>

    const x: int := 0;
    const z: int := 1;
    const secret: int := 2;
    const NUM_VARS := 3;

    constructor()
        ensures Valid()
        ensures Secure()
    {
        Vars := [V(0,Low), V(0,Low), V(10,High)];
    }

    function method LevelsWith(vars: seq<V>): seq<L>
        requires |vars| == NUM_VARS
        ensures |LevelsWith(vars)| == NUM_VARS
    {
        // x z secret
        [if vars[z].v % 2 == 0 then Low else High, Low, High]
    }

    function method Levels(): seq<L>
        reads this
        requires |Vars| == NUM_VARS
    {
        LevelsWith(Vars)
    }

    predicate method Valid()
        reads this
    {
        |Vars| == NUM_VARS
        // && Vars[secret].gamma == High
    }

    predicate method Secure()
        reads this
    {
        Valid()
        &&
        var levels := Levels();
        forall i | 0 <= i < |Vars| :: leq(Vars[i].gamma, levels[i])
    }

    method Store(index: int, v: V)
        modifies this
        requires Valid()
        requires 0 <= index < |Vars|
        requires leq(v.gamma, Levels()[index])

        ensures Vars == old(Vars)[index := v]
        // note: does not perform "secure update" check on controlled variables.
        // Secure() should be asserted after invoking this method.
    {
        Vars := Vars[index := v];
    }

    static function method add(x: int, y: int): int
    {
        x + y
    }

    method test()
        modifies this
        requires Secure()

    {

        var e := lift(Vars[secret], pure(10), add);
        // assert leq(e.gamma, Levels()[x]);

        Vars := Vars[x := e];
        // Vars, Gammas := Vars.(x := e), Gammas.(x := Gamma_e);
        // assert Secure();
    }

    method sync_write()
        modifies this
        requires Secure()
        requires Vars[z].v % 2 == 0

        ensures Secure()
    {
        sync_write_R();

        var z' := lift(Vars[z], pure(1), add);
        Store(z, z');
        assert Secure();

        sync_write_R();

        var x' := Vars[secret];
        Store(x, x');
        assert Secure();

        sync_write_R();

        var x'' := pure(0);
        Store(x, x'');
        assert Secure();

        sync_write_R();

        var z'' := lift(Vars[z], pure(1), add);
        Store(z, z'');
        assert Secure();

        sync_write_R();
    }

    method sync_write_R()
        modifies this
        requires Valid()
        ensures Valid()
        ensures public_read_G()

    twostate predicate public_read_G()
        reads this
        requires old(Valid())
        requires Valid()
    {
        leq(old(Vars[x].gamma), Vars[x].gamma)
        && Vars[z] == old(Vars[z])
    }

    method public_write(data: V)
        modifies this
        requires Secure()
        requires data.gamma == Low
        ensures Secure()
    {
        Store(x, data);
        assert Secure();
    }

    method public_read() returns (r2: V)
        decreases *
        requires Secure()
        ensures Secure()
        ensures r2.gamma == Low
    {
        var r1: V;
        {
            r1 := Vars[z];
            while (r1.v % 2 != 0)
                decreases *
                invariant r1 == Vars[z];
            {
                r1 := Vars[z];
            }
            r2 := Vars[x];
        }
        while (Vars[z].v != r1.v)
            decreases *
            invariant r1 == Vars[z];
            invariant r2 == Vars[x];
        {
            r1 := Vars[z];
            while (r1.v % 2 != 0)
                decreases *
                invariant r1 == Vars[z];
            {
                r1 := Vars[z];
            }
            r2 := Vars[x];
        }
    }


}
