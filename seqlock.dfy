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
// type Vars = Frame<Val<L, int>> // mapping of variable to their values.

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
type Vars = Frame<V>
datatype Idx = X | Z | SECRET
class SeqLock {
    var Vars: Vars;
    const one := 1;

    constructor()
        ensures Secure()
    {
        Vars := Frame(V(0,Low), V(0,Low), V(10,High));
    }

    function method Levels(vars: Vars := Vars): Frame<L>
        reads this
    {
        Frame(if vars.z.v % 2 == 0 then Low else High, Low, High)
    }

    predicate method Secure(vars: Vars := Vars)
        reads this
    {
        var levels := Levels(vars);
        leq(vars.x.gamma, levels.x)
        && leq(vars.z.gamma, levels.z)
        && leq(vars.secret.gamma, levels.secret)
    }

    function method Read(index: Idx): V
        reads this
    {
        match index case X => Vars.x case Z => Vars.z case SECRET => Vars.secret
    }

    method Store(index: Idx, v: V)
        modifies this
        requires leq(v.gamma, match index case X => Levels().x case Z => Levels().z case SECRET => Levels().secret)

        ensures Vars == match index case X => old(Vars).(x := v) case Z => old(Vars).(z := v) case SECRET => old(Vars).(secret := v)
        // note: does not perform "secure update" check on controlled variables.
        // Secure() should be asserted after invoking this method.
    {
        Vars := match index case X => (Vars).(x := v) case Z => (Vars).(z := v) case SECRET => (Vars).(secret := v);
    }

    static function method add(x: int, y: int): int
    {
        x + y
    }

    method test()
        modifies this
        requires Secure()

    {
        Store(SECRET, V(1, Low));

        // var e := lift(Vars.secret, pure(10), add);
        // assert leq(e.gamma, Levels()[x]);

        // Vars := Vars.x := e;
        // Vars, Gammas := Vars.(x := e), Gammas.(x := Gamma_e);
        // assert Secure();
    }

    method sync_write()
        modifies this
        requires Secure()
        requires Vars.z.v % 2 == 0

        ensures Secure()
    {
        // sync_write_R();
        Rely(public_read_G);

        label 1: var z' := lift(Read(Z), pure(1), add);
        Store(Z, z');
        assert Guar@1(sync_write_G);
        assert Secure();

        Rely(public_read_G);
        // sync_write_R();
        // label l:
        // modify this;
        // assume Valid() && public_read_G(Vars@l);

        label 2: var x' := Vars.secret;
        Store(X, x');
        assert Guar@2(sync_write_G);
        assert Secure();

        Rely(public_read_G);

        label 3: var x'' := pure(0);
        Store(X, x'');
        assert Guar@3(sync_write_G);
        assert Secure();

        Rely(public_read_G);

        label 4: var z'' := lift(Vars.z, pure(1), add);
        Store(Z, z'');
        assert Guar@4(sync_write_G);
        assert Secure();

        Rely(public_read_G);
    }

    method Rely(rely: (Vars) ~> bool)
        modifies this
        requires rely.requires(Vars)
        ensures rely.requires(old(Vars))
        ensures rely(old(Vars))

    twostate predicate Guar(guar: (Vars) ~> bool)
        reads this, guar.reads
        requires guar.requires(old(Vars))
    {
        guar(old(Vars))
    }

    predicate method public_read_G(old_vars: Vars)
        reads this
    {
        // true
        leq(Vars.x.gamma, (old_vars.x.gamma))
        && Vars.z == old_vars.z
    }

    predicate method sync_write_G(Old: Vars)
        reads this
    {
        Vars.z.v >= Old.z.v
    }

    method public_write(data: V)
        modifies this
        requires Secure()
        requires data.gamma == Low
        ensures Secure()
    {
        Store(X, data);
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
            r1 := Vars.z;
            while (r1.v % 2 != 0)
                decreases *
                invariant r1 == Vars.z;
                invariant Secure();
            {
                r1 := Vars.z;
            }
            r2 := Vars.x;
        }
        while (Vars.z.v != r1.v)
            decreases *
            invariant r1 == Vars.z;
            invariant r2 == Vars.x;
            invariant Secure();
        {
            r1 := Vars.z;
            while (r1.v % 2 != 0)
                decreases *
                invariant r1 == Vars.z;
                invariant Secure();
            {
                r1 := Vars.z;
            }
            r2 := Vars.x;
        }
    }


}
