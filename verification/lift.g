autkey := function(g, autcls_lookup)
    local m, i, orbs;
    m := Order(g);
    orbs := LookupDictionary(autcls_lookup, m);
    for i in [1..Length(orbs)] do
        if g in orbs[i] then
            return [m, i];
        fi;
    od;
    return fail;
end;

LiftGal := function(opts, proj, is_char, algorithm)
    # proj should be a surjective group homomorphism whose kernel is a p-group (usually minimal)
    # opts should be list of tuples in the codomain of proj representing all of the orbits of [sigma, tau, x0, x1...]
    # under automorphisms
    # algorithm should be an integer between 0 and 6 (inclusive).  0 means automatic selection, while the other options allow for manual selection.
    # Odd means use Orbits on the preimages (usually faster if the kernel of proj is small), while even means to build orbits on the lifts using successive stabilizers.  Defaults to first option when kernel has size at most 5.
    # 1 or 2 means use Orbits to remove duplicates in the case that the kernel is not characteristic (impractical if the sizes of the orbits ends up large, which is hard to predict)
    # 3 or 4 means use a lookup table based on autjugacy class to remove duplicates (much better than 1 or 2 when there are large orbits, but bad if the size of the group is large since it involves listing all of the elements of G and putting them into autjugacy classes via Orbits(Aut(G), G))
    # 5 or 6 means use a lookup table  based on order to remove duplicates (also fine when there are large orbits, better for large groups but slower if there end up being many options).
    # for a default, the lookup table using the 5/6 method is constructed and then the sizes of the buckets are compared to the sizes of the groups in deciding whether to switch to 3/4.  1/2 is never the default.
    local G, T, N, p, AG, SG, AT, Aproj, K, extended_opts, lifted, r, rr, base, vec, baselifts, stabs, S, preimages, orb_lookup, save_orbs, i, new_baselifts, new_stabs, looked, g, m, mm, orders, by_order, autcls_lookup, by_key, key, keys, orbs, num_comps;
    if Length(opts) = 0 then
        return [];
    fi;
    G := Source(proj);
    T := Range(proj);
    N := Kernel(proj);
    p := PrimeDivisors(Order(N))[1];
    AG := AutomorphismGroup(G);
    if is_char then
        SG := AG;
    else
        SG := Stabilizer(AG, Set(N), OnSets);
    fi;
    # SG is the stabilizer of N, and is the largest subgroup of AG that naturally maps to AT
    AT := AutomorphismGroup(T);
    Aproj := GroupHomomorphismByImages(SG, AT, List(GeneratorsOfGroup(SG), x->InducedAutomorphism(proj, x)));
    K := Kernel(Aproj);
    # K acts naturally on the fibers of proj

    # We need a left transversal, not a right transversal, so we switch by taking inverses
    extended_opts := ListX(opts, List(RightTransversal(AT, Image(Aproj)), x->x^-1), OnTuples);
    # When Aproj is not surjective, we need to enlarge opts since there are automorphisms of T
    # that are not induced by automorphisms of G.

    if (algorithm = 0 and Order(N) <= 5) or algorithm = 1 or algorithm = 3 or algorithm = 5 then
        # We filter on tau^sigma = tau^p before taking Orbits because it's cheap;
        # Filter on generating all of G and CheckRel afterward since they're more expensive
        lifted := List(Orbits(K, Filtered(Concatenation(List(extended_opts, base->Cartesian(List(base, x->PreImages(proj, x))))), x->(x[2]^x[1] = x[2]^p)), OnTuples), x->x[1]);
        lifted := Filtered(lifted, x->(Index(G, Subgroup(G, x)) = 1 and CheckRel(x)));
    else
        lifted := [];
        # lifted will hold the final answer: valid lifts of tuples to G
        r := Length(opts[1]);
        if IsPrimePowerInt(Order(G)) then
            rr := r - 1;
        else
            rr := r;
        fi;
        # Things will probably go poorly with a large N, but maybe this will keep us from running out of memory
        save_orbs := (Order(N)^rr < 600000);
        for base in extended_opts do
            # For each base, we build lifts by choosing each entry from orbit representatives under the action of the stabilizer of the entries chosen so far
            vec := [];
            # vec will be progressively updated, and added to lifted when it satisfies the constraints
            baselifts := [];
            # baselifts will hold possibilities for the entries of vec
            stabs := [];
            # stabs will hold the corresponding stabilizers
            S := K;
            # S will be updated as we build lifts below so that it is the stabilizer of the part of the lift that has been fixed so far.
            preimages := List(base, x->PreImages(proj, x));
            # these contain the possibilities for each coordinate of the lifts.  We could just loop over the cartesian product, but this could be very large so we try to progressively trim possibilities.
            orb_lookup := NewDictionary([K,1], true);
            # orb_lookup will store Orbit results, which may be reused multiple times
            # But if N is too large we disable caching so that we don't run out of memory (see save_orbs above)

            while true do
                i := Length(baselifts);
                if Length(vec) < r then
                    # vec is not long enough, so we need to add an entry to the end from the valid possibilities (based on position)
                    # This case occurs at the begining of the loop, but also after vec is trimmed in the final option
                    if i <= Length(vec) then
                        # We don't currently have the possibilities for the next entry, so we need to compute them
                        i := i + 1;
                        if save_orbs and i > 2 and KnowsDictionary(orb_lookup, [S, i]) then
                            # We only use orb_lookup for i > 2 in order to simplify the logic for testing tau^sigma = tau^p
                            looked := LookupDictionary(orb_lookup, [S, i]);
                            new_baselifts := List(looked[1]);
                            new_stabs := List(looked[2]);
                        else
                            new_baselifts := List(Orbits(S, preimages[i]), O->O[1]);
                            if save_orbs and i > 2 then
                                new_stabs := List(new_baselifts, x->Stabilizer(S, x));
                                # We store new_baselifts and new_stabs for later
                                AddDictionary(orb_lookup, [S, i], [List(new_baselifts), List(new_stabs)]);
                            fi;
                        fi;
                        if i = 2 then
                            # Need to ensure that tau^sigma = tau^p
                            while true do
                                new_baselifts := Filtered(new_baselifts, x->(x^vec[1] = x^p));
                                if Length(new_baselifts) > 0 or Length(baselifts[1]) = 0 then
                                    # In the first case we're done: we have valid possibilites for tau
                                    # In the second case there are no more valid sigma remaining, so we're done with this choice of base from extended_opts.
                                    break;
                                fi;
                                # There are no valid tau for this sigma, so we need to proceed to the next sigma.
                                vec[1] := Remove(baselifts[1], 1);
                                S := Remove(stabs[1], 1);
                                new_baselifts := List(Orbits(S, preimages[i]), O->O[1]);
                            od;
                            if Length(new_baselifts) = 0 then
                                # No valid pairs sigma,tau left
                                break;
                            fi;
                        fi;
                        if i <= 2 or not save_orbs then
                            # We held off on computing stabilizers for sigma and tau, so we do it now
                            new_stabs := List(new_baselifts, x->Stabilizer(S, x));
                        fi;
                        # Save new_baselifts and new_stabs for future iteration
                        Add(baselifts, new_baselifts);
                        Add(stabs, new_stabs);
                    fi;
                    # Set the next entry of vec and corresponding S
                    vec[Length(vec)+1] := Remove(baselifts[i], 1);
                    S := Remove(stabs[i], 1);
                elif i = 0 then
                    # vec has full length, but we've recursed down and removed all of the entries of baselifts.
                    # This is the end of iteration, so we break and proceed to the next base from extended_opts.
                    break;
                elif Length(baselifts[i]) = 0 then
                    # There are no more entries left in baselifts, so we remove the last entry and continue
                    Remove(baselifts);
                    Remove(stabs);
                    continue;
                else
                    # We update the appropriate entry of vec from the list of possibilities (and change S accordingly)
                    if Length(vec) > i then
                        vec := List([1..i], m->vec[m]);
                    fi;
                    vec[i] := Remove(baselifts[i], 1);
                    S := Remove(stabs[i], 1);
                fi;
                if Length(vec) = r and Index(G, Subgroup(G, vec)) = 1 and CheckRel(vec) then
                    # We add vec to the final answer.  We need to apply List to get a copy because vec is changing.
                    Add(lifted, List(vec));
                fi;
            od;
        od;
    fi;
    if Length(lifted) = 0 then
        return lifted;
    fi;
    if Order(SG) <> Order(AG) then
        # It is possible that some of these are equivalent to each other under the action of AG, even though they are distinct under the action of SG.  For example, there are 4 orbits for C3 but only one for C3^2.
        # This is what we'd like to do, but it's too expensive since the orbits can be very large.
        if algorithm = 1 or algorithm = 2 then
            lifted := List(Orbits(AG, lifted, OnTuples), O->O[1]);
        else
            # So instead we will build a lookup table to divide lifted into clusters,
            # Then use RepresentativeAction to check if in same orbit
            # Unless algorithm is specified as 3 or 4, we start by building the table using just order
            if not (algorithm = 3 or algorithm = 4) then
                by_key := NewDictionary(List(lifted[1], x->1), true);
                keys := [];
                for vec in lifted do
                    key := List(vec, x->Order(x));
                    if not (key in keys) then
                        Add(keys, key);
                    fi;
                    if not KnowsDictionary(by_key, key) then
                        AddDictionary(by_key, key, []);
                    fi;
                    Add(LookupDictionary(by_key, key), [vec]);
                od;
            fi;
            if algorithm = 0 and Order(G) < 20000 then
                # We compare the worst case number of RepresentativeAction calls to the size of the group
                num_comps := Sum(List(keys, key->Length(LookupDictionary(by_key, key)) * (Length(LookupDictionary(by_key, key)) - 1) / 2));
                # The following is a very rough guess as to when to do the further work to group by autjugacy.
                if 2*num_comps > Order(G) then
                    algorithm := 4;
                fi;
            fi;
            if algorithm = 3 or algorithm = 4 then
                # We try to break lifted up into smaller pieces based on autjugacy classes
                by_order := NewDictionary(1, true);
                orders := [];
                for g in G do
                    m := Order(g);
                    if not (m in orders) then
                        Add(orders, m);
                    fi;
                    if not KnowsDictionary(by_order, m) then
                        AddDictionary(by_order, m, []);
                    fi;
                    Add(LookupDictionary(by_order, m), g);
                od;
                autcls_lookup := NewDictionary(1, true);
                for m in orders do
                    AddDictionary(autcls_lookup, m, Orbits(AG, LookupDictionary(by_order, m)));
                od;
                by_key := NewDictionary(List(lifted[1], x->[1,1]), true);
                keys := [];
                for vec in lifted do
                    key := List(vec, x->autkey(x, autcls_lookup));
                    if not (key in keys) then
                        Add(keys, key);
                    fi;
                    if not KnowsDictionary(by_key, key) then
                        AddDictionary(by_key, key, []);
                    fi;
                    Add(LookupDictionary(by_key, key), [vec]);
                od;
            fi;

            # Either way, we can now use the by_key dictionary to compute the orbits.
            lifted := [];
            for key in keys do
                m := 1;
                orbs := LookupDictionary(by_key, key);
                while m < Length(orbs) do
                    for mm in [m+1..Length(orbs)] do
                        g := RepresentativeAction(AG, orbs[m][1], orbs[mm][1], OnTuples);
                        if g <> fail then
                            orbs[m] := Concatenation(orbs[m], orbs[mm]);
                            Unbind(orbs[mm]);
                        fi;
                    od;
                    orbs := Compacted(orbs);
                    m := m + 1;
                od;
                lifted := Concatenation(lifted, List(orbs, O->O[1]));
            od;
        fi;
    fi;
    return lifted;
end;

