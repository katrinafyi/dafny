class Graph {
    constructor () {
        var s : map<int,int> := map[];
        assert |s| == 0;

    }

}

datatype Person = P(id: int)

datatype Meeting = M(time: nat, person: Person)



predicate sorted(s: seq<Meeting>) {
    if s == [] then
        true
    else
        (forall i | 1 <= i < |s| :: s[0].time <= s[i].time)
        && sorted(s[1..])
}

predicate sortedPairwise(s: seq<Meeting>) {
    forall i | 0 <= i < |s|-1 :: s[i].time <= s[i+1].time
}

predicate sortedProduct(s: seq<Meeting>) {
    forall i | 0 <= i < |s| ::
    forall j | 0 <= j < |s| ::
    i <= j ==> s[i].time <= s[j].time
}

predicate strictIncreasing(s: seq<Meeting>)
{
    forall i | 0 <= i < |s|-1 ::
    s[i].time < s[i+1].time
}

lemma strictIncreasing2(s: seq<Meeting>)
    requires strictIncreasing(s)

    ensures
        forall i | 0 <= i < |s| ::
        forall j | i < j < |s| ::
        s[i].time < s[j].time
{
    if |s| < 2 {
    } else if s[0].time < s[1].time {
        strictIncreasing2(s[1..]);
    } else {
    }

}

lemma sortLemma(s: seq<Meeting>)
    requires sorted(s)
    ensures sortedPairwise(s)
{
    if |s| < 2 {

    } else {
        sortLemma(s[1..]);
    }
}

lemma sortSubseq(s: seq<Meeting>, i: nat)
    requires sorted(s)
    requires 0 <= i <= |s|
    ensures sorted(s[i..])
{
    if |s| < 2 {
    } else if i == 0 {
    } else {
        sortSubseq(s, i-1);
    }

}


lemma sortLemma2(s: seq<Meeting>)
    requires sorted(s)
    ensures sortedProduct(s)
{
    if |s| < 2 {

    } else {
        sortLemma2(s[1..]);
    }
}

predicate distinct<T>(s: seq<T>) {
    forall i | 0 <= i < |s| ::
    forall j | 0 <= j < |s| ::
    i != j ==> s[i] != s[j]
}

lemma increasingLemma(s: seq<Meeting>, p: Person)
    requires forall m | m in s :: m.person == p
    requires sorted(s)
    requires distinct(s)
    ensures strictIncreasing(s)
{
}

class Finder {
    var people: set<Person>;
    var next: map<Person, set<Person>>;
    var availableMeetings: seq<Meeting>;
    var first: Person;
    var last: Person;


    ghost var MAX_TIME : nat;
    ghost var MEETINGS : set<Meeting>;
    ghost var Repr: set<object>;

    constructor(people: set<Person>, next: map<Person, set<Person>>, availableMeetings: seq<Meeting>, first: Person, last: Person)
        requires sorted(availableMeetings)
        requires distinct(availableMeetings)
        requires people == next.Keys
        requires (forall m | m in availableMeetings :: m.person in people)
        requires (forall p | p in next.Keys :: next[p] <= people)
        requires first in people && last in people
        ensures Valid()
    {
        this.people := people;
        this.next := next;
        this.availableMeetings := availableMeetings;
        this.first := first;
        this.last := last;
        this.MEETINGS := set m | m in availableMeetings;
        if |availableMeetings| > 0
        {
            MAX_TIME := availableMeetings[|availableMeetings|-1].time + 1;
            sortLemma2(availableMeetings);
        }
        else
        {
            MAX_TIME := 1;
        }
    }

    predicate Valid()
        reads this
    {
        sorted(availableMeetings)
        && distinct(availableMeetings)
        && people == next.Keys
        && (forall m | m in availableMeetings :: m.person in people)
        && (forall p | p in next.Keys :: next[p] <= people)
        && (forall m | m in availableMeetings :: m.time < MAX_TIME)
        && first in people
        && last in people
        && MEETINGS == set m | m in availableMeetings
        && FirstMeetings() !! MiddleMeetings()
        && MiddleMeetings() !! LastMeetings()
    }

    predicate IsSchedule(s: seq<Meeting>)
        reads this
        requires Valid()
    {
        if |s| == 0 then
            false
        else
            s[0].person == first && s[|s|-1].person == last
            && forall m | m in s :: m in availableMeetings
            && forall i | 0 <= i < |s|-1 ::
                (s[i].time < s[i+1].time
                && s[i].person in people
                && s[i+1].person in next[s[i].person])
    }


    function {:opaque} FirstMeetings(): set<Meeting>
        reads this
        ensures FirstMeetings() <= MEETINGS
        ensures forall x | x in FirstMeetings() :: x.person == first
    {
        set m | m in MEETINGS && m.person == first
    }

    function {:opaque} LastMeetings(): set<Meeting>
        reads this
        ensures LastMeetings() <= MEETINGS
        ensures forall x | x in LastMeetings() :: x.person == last
    {
        set m | m in MEETINGS && m.person == last
    }
    function {:opaque} MiddleMeetings(): set<Meeting>
        reads this
        ensures MiddleMeetings() <= MEETINGS
        ensures forall x | x in MiddleMeetings() :: x.person != last && x.person != first
    {
        set m | m in MEETINGS && m.person != last && m.person != first
    }

    function ScheduleTime(s: seq<Meeting>): nat
    {
        if |s| == 0 then
            1
        else
            s[0].time + ScheduleTime(s[1..])
    }

    function SchedulePeople(s: seq<Meeting>): set<Person>
    {
        set m | m in s :: m.person
    }

    predicate MinSchedule(s: seq<Meeting>)
        reads this
        requires Valid()
    {
        IsSchedule(s) &&
        forall s' | IsSchedule(s') :: ScheduleTime(s) <= ScheduleTime(s')
    }

    function FindPeopleResult(): set<Person>
        reads this
        requires Valid()
    {
        set p | p in people && (exists s | MinSchedule(s) :: p in SchedulePeople(s))
    }

    function MeetingsWithPersonAfterTimeHelper(p: Person, t:nat, ms: seq<Meeting>): seq<nat>
        reads this
        requires Valid()
        requires p in people
        requires sorted(ms)

    {
        if ms == [] then
            []
        else if ms[0].person == p && ms[0].time > t then
            [ms[0].time] + MeetingsWithPersonAfterTimeHelper(p, t, ms[1..])
        else
            MeetingsWithPersonAfterTimeHelper(p, t, ms[1..])
    }

    function MeetingsWithPersonAfterTime(p: Person, t: nat): seq<nat>
        reads this
        requires Valid()
        requires p in people

        ensures (set t' | t' in MeetingsWithPersonAfterTime(p, t) :: M(t',p)) <= MEETINGS

    {
        MeetingsWithPersonAfterTimeHelper(p, t, availableMeetings)
    }

    function NextMeetingToPerson(m1: Meeting, p2: Person): map<Meeting, nat>
        reads this
        requires Valid()
        requires m1 in availableMeetings
        requires p2 in people

        ensures |NextMeetingToPerson(m1,p2)| <= 1
        ensures NextMeetingToPerson(m1,p2).Keys <= MEETINGS
        ensures forall m | m in NextMeetingToPerson(m1,p2) :: m.person == p2 && m.time > m1.time
    {
        var times := MeetingsWithPersonAfterTime(p2, m1.time);
        if times == [] then
            map[]
        else
            // var t := Minimum(times);
            // map[M(t, p2) := t - m1.time]
            map[]
    }

    function NextMeetings(m1: Meeting): map<Meeting, nat>
        reads this
        requires Valid()
        requires m1 in availableMeetings
    {
        map p2, m2, t : nat |
            m2 in availableMeetings
            && p2 in people
            && t < MAX_TIME
            && (m2,t) in NextMeetingToPerson(m1, p2).Items
            :: m2 := t
    }

    function EmptyMeetings(source: Meeting, sink: Meeting): map<Meeting, map<Meeting, nat>>
        reads this
        requires Valid()

        requires source != sink
        requires source !in MEETINGS
        requires sink !in MEETINGS

        ensures source in EmptyMeetings(source, sink).Keys
        ensures sink in EmptyMeetings(source, sink).Keys
        ensures MEETINGS <= EmptyMeetings(source, sink).Keys
    {
        reveal FirstMeetings();
        reveal MiddleMeetings();
        reveal LastMeetings();
        map[sink := map[]]
        + map[source := map m | m in FirstMeetings() :: 0]
        + (map m | m in FirstMeetings() :: map[])
        + (map m | m in MiddleMeetings() :: map[])
        + (map m | m in LastMeetings() :: map[sink := 0])
    }


    method InitSourceSink(source: Meeting, sink: Meeting)
        returns (succs: map<Meeting, map<Meeting, nat>>)

        requires Valid()
        requires source != sink
        requires source !in availableMeetings
        requires sink !in availableMeetings

        ensures succs.Keys == {source, sink} + MEETINGS
        ensures succs[sink] == map[]
        ensures succs[source] == map m | m in FirstMeetings() :: 0
        ensures forall m | m in MEETINGS - LastMeetings() :: succs[m] == map[]
        ensures forall m | m in LastMeetings() :: succs[m] == map[sink := 0]
    {
        succs := map m1 | m1 in availableMeetings :: map[];
        succs := succs[source := map[]][sink := map[]];

        var i := |availableMeetings| - 1;
        while (i >= 0)
            invariant i+1 >= 0

            invariant source !in availableMeetings
            invariant sink !in availableMeetings
            invariant succs.Keys == {source, sink} + MEETINGS
            invariant succs[sink] == map[]
            invariant succs[source] == map m | m in FirstMeetings() && m in availableMeetings[i+1..] :: 0
            invariant forall m | m in MEETINGS - LastMeetings() :: succs[m] == map[]
            invariant forall m | m in LastMeetings() && m in availableMeetings[..i+1] :: succs[m] == map[]
            invariant forall m | m in LastMeetings() && m in availableMeetings[i+1..] :: succs[m] == map[sink := 0]
        {
            var m1 := availableMeetings[i];
            if (m1.person == first) {
                assert m1 in FirstMeetings() by { reveal FirstMeetings(); }
                succs := succs[source := succs[source][m1 := 0]];
            }
            if (m1.person == last) {
                assert m1 in LastMeetings() by { reveal LastMeetings(); }
                succs := succs[m1 := succs[m1][sink := 0]];
            }
            i := i - 1;
        }
    }

    // method MeetingsWithPerson(p: Person)
    //     requires Valid()

    //     ensures distinct(ms)
    //     ensures forall m | m in availableMeetings && m.person == p :: m in ms
    //     ensures forall m | m in ms :: m in availableMeetings && m.person == p
    // {
    //     var ms := [];
    //     var i := 0;
    //     while i < |availableMeetings|
    //     {

    //         i := i + 1;
    //     }


    // }

    function MeetingsAfter(p: Person, i: nat): seq<Meeting>
        reads this
        requires Valid()
        requires 0 <= i <= |availableMeetings|

        requires p in people
        decreases |availableMeetings| - i

        ensures forall t | t in MeetingsAfter(p,i) :: t in availableMeetings[i..] && t.person == p
        ensures forall m | m in availableMeetings[i..] && m.person == p :: m in MeetingsAfter(p,i)
        ensures MeetingsAfter(p,i) == [] ==> forall j | i < j < |availableMeetings| :: availableMeetings[j].person != p
        ensures sorted(MeetingsAfter(p,i))
        ensures distinct(MeetingsAfter(p,i))
        ensures strictIncreasing(MeetingsAfter(p,i))
    {
        if i >= |availableMeetings| then
            []
        else if availableMeetings[i].person == p then
            var m := availableMeetings[i];
            var after := MeetingsAfter(p, i+1);
            sortSubseq(availableMeetings, i);
            sortLemma(availableMeetings[i..]);

            increasingLemma(after, p);

            [m] + after
        else
            MeetingsAfter(p, i+1)
    }

    function NextMeetingAfter(p: Person, i: nat): seq<Meeting>
        reads this
        requires Valid()
        requires 0 <= i <= |availableMeetings|
        requires p in people

        ensures |NextMeetingAfter(p,i)| <= 1
        ensures NextMeetingAfter(p, i) == [] <==> MeetingsAfter(p,i) == []
        ensures NextMeetingAfter(p, i) != [] ==> forall j | i < j < |availableMeetings| && availableMeetings[j].person == p :: availableMeetings[j].time > NextMeetingAfter(p,i)[0].time
    {
        var after := MeetingsAfter(p, i);
        if after == [] then
            []
        else
            [after[0]]
    }

    method ConnectNextGraph(source: Meeting, sink: Meeting, succs: map<Meeting, map<Meeting, nat>>)
        returns (succs': map<Meeting, map<Meeting, nat>>)

        requires Valid()

        requires source != sink
        requires source !in availableMeetings
        requires sink !in availableMeetings

        requires succs.Keys == {source, sink} + MEETINGS
        requires succs[sink] == map[]
        requires succs[source] == map m | m in FirstMeetings() :: 0
        requires forall m | m in MEETINGS - LastMeetings() :: succs[m] == map[]
        requires forall m | m in LastMeetings() :: succs[m] == map[sink := 0]

        ensures {source, sink} + MEETINGS == succs'.Keys
        ensures succs'[sink] == map[]
        ensures succs'[source] == map m | m in FirstMeetings() :: 0

        // ensures forall m | m in MEETINGS - LastMeetings() :: succs'[m] == NextMeetings(m)
        // ensures forall m | m in LastMeetings() :: succs'[m] == NextMeetings(m)[sink := 0]
    {
        succs' := succs;

        var lastMeeting : map<Person, seq<Meeting>> := map p | p in people :: [];

        var t := MAX_TIME;
        var i := |availableMeetings| - 1;
        while (i >= 0)
            invariant i+1 >= 0
            invariant lastMeeting.Keys == people
            invariant forall p | p in people :: lastMeeting[p] == MeetingsAfter(p, i+1)

            invariant forall m | m in availableMeetings[i+1..]
                :: succs'[m] == succs[m] + NextMeetings(m)
        {
            var m1 := availableMeetings[i];
            t := m1.time;

            lastMeeting := lastMeeting[m1.person := [m1] + lastMeeting[m1.person]];

            // var next_remaining := next[m1.person];
            // while next_remaining != {}
            // {
            //     var p2 :| p2 in next_remaining;

            //     next_remaining := next_remaining - {p2};
            // }


            i := i - 1;
        }


    }



    method FindPeople(first: Person, last: Person)
        returns (result: set<Person>)
        requires Valid()
        requires first in people && last in people
        //ensures result == FindPeopleResult()
    {
        var maxPerson := 0;
        {
            var p := people;
            while p != {}
                invariant (forall p' | p' in people - p :: p'.id <= maxPerson)
            {
                var i: Person :| i in p;
                maxPerson := if maxPerson < i.id then i.id else maxPerson;
                p := p - {i};
            }
        }
        assert (forall p | p in people :: p.id <= maxPerson);

        var sourcePerson := P(maxPerson + 1);
        var sinkPerson := P(maxPerson + 2);

        assert sourcePerson !in people && sinkPerson !in people
            && sourcePerson != sinkPerson;

        var source := M(0, sourcePerson);
        var sink := M(0, sinkPerson);

        var lastMeeting: map<Person, seq<Meeting>> := map p | p in people :: [];

        ghost var meetings := set m | m in availableMeetings;
        ghost var sourceOrSink := {source, sink};
        ghost var meetings2 := meetings + sourceOrSink;

        var succs := InitSourceSink(source, sink);


        // {

        //     var i := |availableMeetings| - 1;
        //     while (i >= 0)
        //         invariant people == lastMeeting.Keys
        //         invariant forall x | x in lastMeeting.Values :: sorted(x)
        //         invariant sorted(availableMeetings)
        //         invariant
        //             forall p | p in lastMeeting.Keys ::
        //             forall m | m in lastMeeting[p] ::
        //             i >= 0 ==> availableMeetings[i].time <= m.time
        //         invariant
        //             forall m1 | m1 in succs.Keys ::
        //             forall m2 | m2 in succs[m1].Keys ::
        //             m1 in availableMeetings && m2 in availableMeetings
        //             ==> m1.time < m2.time
        //     {
        //         var m1 := availableMeetings[i];

        //         lastMeeting := lastMeeting[m1.person := [m1] + lastMeeting[m1.person]];

        //         var remaining := next[m1.person];
        //         while remaining != {}
        //             // invariant (set m2 | m2 in meetings2 && m2.person in next[m1.person] && m2.person !in remaining)
        //             //     == succs[m1].Keys
        //         {
        //             var p2 :| p2 in remaining;


        //             remaining := remaining - {p2};
        //         }

        //         i := i - 1;
        //         sortLemma(availableMeetings);
        //     }
        // }



    }
}
