datatype L = Low | High

predicate leq(l1:L,l2:L) {
    (l1 == Low || l2 == High)
}

// upper bound on l1 and l2
function join(l1:L,l2:L):L {
    if leq(l1,l2) then l2 else l1
}
// lower bound on l1 and l2
function meet(l1:L,l2:L):L {
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


datatype Frame<T> = Frame(x: T, z: T, secret: T, leak: T)
datatype Val<L, T> = V(v: T, gamma: L)
// type Vars = Frame<Val<L, int>> // mapping of variable to their values.

function lift<T>(v1: Val<L,T>, v2: Val<L,T>, f: (T,T) --> T): Val<L,T>
    requires f.requires(v1.v, v2.v)
    ensures leq(v1.gamma,lift(v1,v2,f).gamma)
    ensures leq(v2.gamma,lift(v1,v2,f).gamma)
{
    V(f(v1.v, v2.v), join(v1.gamma, v2.gamma))
}

function pure<T>(t: T): Val<L,T>
{
    V(t,Low)
}



type V = Val<L,int>
type Vars = Frame<V>
datatype Idx = X | Z | SECRET | LEAK
class Spec {
    var Vars: Vars;
    var SVars: Vars;
    var Qspec: bool;
    const VARS := {X, Z, SECRET, LEAK};

    constructor()
        ensures Secure()
    {
        Vars := Frame(V(0,Low), V(0,Low), V(10,High), V(0,Low));
        // SVars := Vars;
    }

    // levels are to be calculated from the concrete "base" Vars.
    function Levels(): Frame<L>
        reads this
    {
        Frame(High, Low, High, Low)
    }

    predicate Secure(globals: Vars := Vars)
        reads this
        ensures X in VARS
        ensures Z in VARS
        ensures SECRET in VARS 
        ensures LEAK in VARS
    {
        (forall v | v in VARS :: leq(Read(v).gamma, Read(v, globals).gamma))
        // && leq(Read(LEAK).gamma, Level(LEAK))
    }

    function Level(index: Idx): L
        reads this
    {
        match index case X => Levels().x case Z => Levels().z case SECRET => Levels().secret case LEAK => Levels().leak
    }

    function Read(index: Idx, vars: Vars := Vars): V
        reads this
    {
        match index case X => vars.x case Z => vars.z case SECRET => vars.secret case LEAK => vars.leak
    }

    method Store(index: Idx, v: V)
        modifies this
        requires leq(v.gamma, Level(index))

        ensures Vars == match index case X => old(Vars).(x := v) case Z => old(Vars).(z := v) case SECRET => old(Vars).(secret := v) case leak => old(Vars).(leak := v)
        // note: does not perform "secure update" check on controlled variables.
        // Secure() should be asserted after invoking this.
    {
        Vars := match index case X => (Vars).(x := v) case Z => (Vars).(z := v) case SECRET => (Vars).(secret := v) case LEAK => Vars.(leak := v);
    }

    static function add(x: int, y: int): int
    {
        x + y
    }

    method nospec()
        modifies this 
        requires Secure()
        requires Vars.z.v == 0
        // requires Vars.leak.gamma == Low
        ensures Secure()
    {
        Rely(R_nospec);
        label 1:
        Store(X, V(-1, Low));
        assert Guar@1(G_nospec);
        assert Secure();

        Rely(R_nospec);
        label 2:
        if (Read(Z).v == 0)
        {
            assert Guar@2(G_nospec);
            assert Secure();

            Rely(R_nospec);
            label 3: var x := Read(X);
            assert Guar@3(G_nospec);
            assert Secure();

            Rely(R_nospec);
            label 4: Store(LEAK, x);
            assert Guar@4(G_nospec);
            assert Secure();
        }
        assert Guar@2(G_nospec);
        assert Secure();
    }

    method spec()
        modifies this 
        requires Secure()
        requires Vars.z.v == 0
        // requires Vars.leak.gamma == Low
        ensures Secure()
    {
        Rely(R_nospec);
        label 1:
        Store(X, V(-1, Low));
        assert Guar@1(G_nospec);
        assert Secure();

        Rely(R_nospec);
        label 2:
        // if (Read(Z).v == 0)
        if (true)
        {
            assert Guar@2(G_nospec);
            assert Secure();

            Rely(R_nospec);
            label 3: var x := Read(X);
            assert Guar@3(G_nospec);
            assert Secure();

            Rely(R_nospec);
            label 4: Store(LEAK, x);
            assert Guar@4(G_nospec);
            assert Secure();
        }
        assert Guar@2(G_nospec);
        assert Secure();
    }


    method R_reflexive()
        ensures R_nospec(Vars)
    {}

    predicate R_nospec(old_vars: Vars)
        reads this
    {
        (old_vars.z.v == 0 ==> old_vars.z == Vars.z && leq(Vars.x.gamma, old_vars.x.gamma))
        && Vars.leak == old_vars.leak
        && leq(Vars.z.gamma, old_vars.z.gamma)
    }

    predicate G_nospec(prev: Vars)
        reads this 
    {
        true
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

    // method sync_write()
    //     modifies this
    //     requires Secure()
    //     requires Vars.z.v % 2 == 0

    //     ensures Secure()
    // {
    //     // sync_write_R();
    //     Rely(public_read_G);

    //     label 1: var z' := lift(Read(Z), pure(1), add);
    //     Store(Z, z');
    //     assert Guar@1(sync_write_G);
    //     assert Secure();

    //     Rely(public_read_G);
    //     // sync_write_R();
    //     // label l:
    //     // modify this;
    //     // assume Valid() && public_read_G(Vars@l);

    //     label 2: var x' := Vars.secret;
    //     Store(X, x');
    //     assert Guar@2(sync_write_G);
    //     assert Secure();

    //     Rely(public_read_G);

    //     label 3: var x'' := pure(0);
    //     Store(X, x'');
    //     assert Guar@3(sync_write_G);
    //     assert Secure();

    //     Rely(public_read_G);

    //     label 4: var z'' := lift(Vars.z, pure(1), add);
    //     Store(Z, z'');
    //     assert Guar@4(sync_write_G);
    //     assert Secure();

    //     Rely(public_read_G);
    // }

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

    predicate public_read_G(old_vars: Vars)
        reads this
    {
        // true
        leq(Vars.x.gamma, (old_vars.x.gamma))
        && Vars.z == old_vars.z
    }

    predicate sync_write_G(Old: Vars)
        reads this
    {
        Vars.z.v >= Old.z.v
    }
}
