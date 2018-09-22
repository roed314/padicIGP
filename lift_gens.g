#
AngleBracket := function(x, rho, p, h, projp)
    local xpow, ans, i;
    xpow := x^h;
    ans := xpow * rho;
    for i in [1..p-2] do
        xpow := xpow^h;
        ans := xpow * rho * ans;
    od;
    return ans^projp;
end;

CurlyBracket := function(x, rho_squared, tau2exp, p, h2, projp, ppartGExp)
    local betarho, xpow, ans, i;
    betarho := PowerModInt(h2, tau2exp, ppartGExp);
    xpow := x;
    ans := xpow * rho_squared;
    for i in [1..p-2] do
        xpow := xpow^betarho;
        ans := ans * xpow * rho_squared;
    od;
    return ans^projp;
end;

X0Relation := function(sigma, tau, x0, p, h, projp)
    if Order(x0) = 1 then
        return x0;
    fi;
    return AngleBracket(x0, tau, p, h, projp)^-1 * x0^sigma;
end;

X1Relation := function(sigma, tau, x1, p, h2, projp, proj2, ppartGExp, abelian_pcore)
    local sigma2, tau2, tau2pm2, tau2pp2, tau2pp, stau2pm2, inner_bracket, outer_bracket, y1;
    if Order(x1) = 1 then
        return x1;
    fi;
    if abelian_pcore then
        return x1^p;
    fi;
    sigma2 := sigma^proj2;
    tau2 := tau^proj2;
    tau2pm2 := tau2^((p-1)/2);
    tau2pp2 := tau2pm2 * tau2;
    tau2pp := tau2pp2^2;
    stau2pm2 := sigma2 * tau2pm2;
    inner_bracket := CurlyBracket(x1, tau2pp^2, p+1, p, h2, projp, ppartGExp);
    outer_bracket := CurlyBracket(inner_bracket, stau2pm2^2, (p-1)/2, p, h2, projp, ppartGExp);
    y1 := x1^tau2pp * inner_bracket^stau2pm2 * outer_bracket^(sigma2*tau2pp2) * outer_bracket^tau2pp2;
    return x1^(p+1) * y1 * x1^-1 * y1^-1;
end;

RelationSatisfied := function(sigma, tau, x0, x1, p, h, h2, projp, proj2, ppartGExp, abelian_pcore)
    return (X0Relation(sigma, tau, x0, p, h, projp) =
            X1Relation(sigma, tau, x1, p, h2, projp, proj2, ppartGExp, abelian_pcore));
end;

# Sonata can't be loaded from Sage for some reason, so we duplicate the implementation of IsIsomorphicGroup
#IsIsomorphicGroup := function(G, H)
#    if IsAbelian(G) <> IsAbelian(H) then
#        return false;
#    fi;
#    if Size(G) <> Size(H) then
#        return false;
#    fi;
#    if Size(G)<=1000 and not (Size(G) in [256,512,768]) then
#	return IdGroup(G)=IdGroup(H);
#    fi;
#    if Size(Centre(G)) <> Size(Centre(H)) then
#	return false;
#    fi;
#    if Size(DerivedSubgroup(G)) <> Size(DerivedSubgroup(H)) then
#	return false;
#    fi;
#    if Collected( List( AsList(G), Order ) ) <>
#	Collected( List( AsList(H), Order ) ) then
#	return false;
#    fi;
#    if IsNilpotent(G) <> IsNilpotent(H) then
#        return false;
#    fi;
#    if IsNilpotent(G) and NilpotencyClassOfGroup(G) <> NilpotencyClassOfGroup(H) then
#        return false;
#    fi;
#    return not ( IsomorphismGroups( G, H ) = fail );
#end;

Component_cyclic := function(m, p)
    local ans, e, me, t, ell;
    ans := [];
    # m should be a prime power
    ell := SmallestRootInt(m);
    if ell = p then
        e := m;
    else
        e := GcdInt(m, p-1);
    fi;
    me := m / e;
    for t in [0..e-1] do
        Append(ans, [[1, t*me]]);
        if me = 1 and GcdInt(t, m) <> 1 then
            Append(ans, [[t, 1]]);
        fi;
    od;
    return ans;
end;

TameGenss_cyclic := function(G, p)
    local genss, m, e, me, s0, t0, max_b, d, b, sigma, bstab, aut, c, tau, x;
    m := Size(G);
    genss := [];
    # The automorphism group is (Z/n)^x
    # The possible sigma (orbits) correspond to the divisors of n
    # e.g. 1,5,7,11 - 2,10 - 3,9 - 4,8 - 6 - 0
    e := GcdInt(m, p-1);
    # the order of tau must be a divisor of p-1 since the tame part is abelian
    me := m / e;
    s0 := MinimalGeneratingSet(G)[1];
    t0 := s0^me;
    # We need divisors of m that are relatively prime to me (so that they can possibly generate)
    max_b := e;
    repeat
        d := GcdInt(max_b, me);
        max_b := max_b / d;
    until d = 1;
    for b in DivisorsInt(max_b) do
        sigma := s0^b;
        bstab := [1];
        for x in [1..b-1] do
            aut := 1+(e/b)*x;
            if GcdInt(aut, e) = 1 then
                Append(bstab, [aut]);
            fi;
        od;
        for c in [0..e-1] do
            if GcdInt(b, c*me) = 1 then
                tau := t0^c;
                Append(genss, [[sigma, tau, One(G), One(G)]]);
            fi;
        od;
    od;
    return genss;
end;

Genss_abelian := function(G, p)
    local genss, m, cyclic_factors, pairs, ainvs, seeni, i, ell, vi, vm, j, vj, agens, x, y, pair, collapse;
    m := Size(G);
    cyclic_factors := [];
    pairs := [];
    ainvs := AbelianInvariants(G);
    seeni := NewDictionary(1, false);
    for i in [1..Length(ainvs)] do
        if KnowsDictionary(seeni, i) then
            continue;
        fi;
        ell := SmallestRootInt(ainvs[i]);
        vi := Valuation(ainvs[i], ell);
        vm := Valuation(m, ell);
        if vi = vm then
            Append(cyclic_factors, [i]);
        else
            for j in [i+1..Length(ainvs)] do
                vj := Valuation(ainvs[j], ell);
                #Print(vi, " ", vj, " ", vm, " ", ainvs[j]);
                if vj > 0 then
                    if vi + vj = vm and (ell = p or (p-1) mod ainvs[i] = 0) then
                        AddDictionary(seeni, j);
                        Append(pairs, [[i,j]]);
                    else
                        # We can't generate
                        return [];
                    fi;
                fi;
            od;
        fi;
    od;
    agens := IndependentGeneratorsOfAbelianGroup(G);
    genss := [[One(G),One(G),One(G),One(G)]];
    for i in cyclic_factors do
        if ainvs[i] mod p = 0 then
            collapse := function(x,y) return [agens[i]^x[1]*y[1],
                                              y[2],
                                              agens[i]^(p*x[2])*y[3],
                                              agens[i]^x[2]*y[4]]; end;
        else
            collapse := function(x,y) return [agens[i]^x[1]*y[1],
                                              agens[i]^x[2]*y[2],
                                              y[3],
                                              y[4]]; end;
        fi;
        genss := ListX(Component_cyclic(ainvs[i], p),
                       genss,
                       collapse);
    od;
    for pair in pairs do
        ell := SmallestRootInt(ainvs[pair[1]]);
        if ell = p then
            if ainvs[pair[1]] = ainvs[pair[2]] then
                genss := List(genss, x -> [agens[pair[1]]*x[1],
                                           x[2],
                                           agens[pair[2]]^p*x[3],
                                           agens[pair[2]]*x[4]]);
            else
                genss := Concatenation(List(genss, x -> [[agens[pair[1]]*x[1],
                                                          x[2],
                                                          agens[pair[2]]^p*x[3],
                                                          agens[pair[2]]*x[4]],
                                                         [agens[pair[2]]*x[1],
                                                          x[2],
                                                          agens[pair[1]]^p*x[3],
                                                          agens[pair[1]]*x[4]]]));
            fi;
        elif (ainvs[pair[1]] = ainvs[pair[2]]) or ((p-1) mod ainvs[pair[2]] <> 0) then
            genss := List(genss, x -> [agens[pair[2]]*x[1],
                                       agens[pair[1]]*x[2],
                                       x[3],
                                       x[4]]);
        else
            genss := Concatenation(List(genss, x -> [[agens[pair[1]]*x[1],
                                                      agens[pair[2]]*x[2],
                                                      x[3],
                                                      x[4]],
                                                     [agens[pair[2]]*x[1],
                                                      agens[pair[1]]*x[2],
                                                      x[3],
                                                      x[4]]]));
        fi;
    od;
    return genss;
end;

TameGenss_nonabelian := function(G, p)
    local genss, TameD, A, covered, TameI, phiTU, Unram, e, f, u0, t0, twist, tpow, a, aorder, b0, b, sigma, tau, d, extra_gen_needed, c, gens, aut, agens; # cangens
    genss := [];
    TameD := DerivedSubgroup(G);
    A := AutomorphismGroup(G);
    #Agens := GeneratorsOfGroup(A);
    #AP := Group(List(Agens, x -> Permutation(x, List(G), OnPoints)));
    covered := NewDictionary([One(G),One(G)],false);
    for TameI in NormalSubgroupsAbove(G, TameD, []) do
        if not IsCyclic(TameI) then
            continue;
        fi;
        phiTU := NaturalHomomorphismByNormalSubgroupNC(G, TameI);
        Unram := Image(phiTU);
        if not IsCyclic(Unram) then
            continue;
        fi;
        e := Size(TameI);
        f := Size(Unram);
        u0 := PreImagesRepresentative(phiTU, MinimalGeneratingSet(Unram)[1]);
        t0 := MinimalGeneratingSet(TameI)[1];
        twist := t0^u0;
        tpow := t0;
        a := 1;
        while tpow <> twist do
            tpow := tpow * t0;
            a := a + 1;
        od;
        aorder := OrderMod(a, e);
        b0 := LogMod(p, a, e);
        if b0 = fail then
            continue;
        fi;
        b0 := b0 mod aorder;
        b := b0;
        while b < f do
            # These bs are the powers of u0 that give the right commutator relation in the tame quotient.
            if GcdInt(f, b) <> 1 then
                b := b + aorder;
                continue;
            fi;
            sigma := u0^b;
            for d in [0..(e-1)] do
                extra_gen_needed := e*f / Order(sigma);
                # extra_gen_needed measures the amount of the TameI subgroup already generated by powers of sigma.
                for c in [0..(e-1)] do
                    if GcdInt(extra_gen_needed, c) <> 1 then
                        continue;
                    fi;
                    tau := t0^c;
                    Assert(0,tau^sigma = tau^p);
                    Assert(0,Size(Subgroup(G,[sigma, tau])) = Size(G));
                    gens := [sigma, tau];
                    #cangens := CanonicalImage(AP, List(gens, x -> PositionCanonical(List(G),x)), OnTuples);
                    #if KnowsDictionary(covered, cangens) then
                    #    continue;
                    #fi;
                    #AddDictionary(covered, cangens);
                    #Append(genss, [gens]);
                    if not KnowsDictionary(covered, gens) then
                        for aut in A do
                            agens := [Image(aut, sigma), Image(aut, tau)];
                            if not KnowsDictionary(covered, agens) then
                                AddDictionary(covered, agens);
                            fi;
                        od;
                        Append(genss, [gens]);
                    fi;
                od;
                sigma := t0 * sigma;
            od;
            b := b + aorder;
        od;
    od;
    return List(genss, x -> [x[1], x[2], One(G), One(G)]);
end;

Genss_base := function(label, G, p)
    local genss;
    if IsAbelian(G) then
        genss := Genss_abelian(G, p);
    else
        genss := TameGenss_nonabelian(G, p);
    fi;
    PrintTo(Concatenation("IGPdata/", label, "_", ViewString(p), "_genss.g"), genss);
    return Length(genss);
end;

AutData := function(G)
    local A, best_cost, N, epi, Q, B, cost, bestN, bestB, bestepi, bestQ, BPiso, BP, Agens, authom, ker_reps, AA, APiso, AP, AAP, cok_reps;
    A := AutomorphismGroup(G);
    best_cost := Size(G)^6;
    for N in NormalSubgroups(G) do
        if Size(N) = 1 then
            continue;
        fi;
        epi := NaturalHomomorphismByNormalSubgroupNC(G, N);
        Q := Image(epi);
        B := AutomorphismGroup(Q);
        cost := Size(N)^4 * Size(B) / Size(A);
        if cost < best_cost or (cost = best_cost and IsCharacteristicSubgroup(G, N)) then
            bestN := N;
            bestB := B;
            bestepi := epi;
            bestQ := Q;
            best_cost := cost;
        fi;
    od;
    N := bestN;
    B := bestB;
    epi := bestepi;
    Q := bestQ;
    BPiso := IsomorphismPermGroup(B);
    BP := Image(BPiso);
    if IsCharacteristicSubgroup(G, N) then
        Agens := GeneratorsOfGroup(A);
        authom := GroupHomomorphismByImagesNC(A, BP, List(Agens, x -> Image(BPiso, InducedAutomorphism(epi, x))));
        ker_reps := List(Kernel(authom));
    else
        AA := Stabilizer(A, Set(N), OnSets);
        APiso := IsomorphismPermGroup(A);
        AP := Image(APiso);
        AAP := Image(APiso, AA);
        Agens := GeneratorsOfGroup(AAP);
        authom := GroupHomomorphismByImagesNC(AAP, BP, List(Agens, x -> Image(BPiso, InducedAutomorphism(epi, PreImage(APiso, x)))));
        ker_reps := Concatenation(List(RightTransversal(AP, AAP), x -> List(Kernel(authom), k -> PreImage(APiso, k * x))));
    fi;
    cok_reps := List(RightTransversal(BP, Image(authom)), x -> PreImage(BPiso, x));
    return best_cost;
end;

LiftGenss_tame := function(label, p)
    local qgens, qsigma, qtau, aut, tau, sigma;
    Read(Concatenation("IGPdata/", label, "_", ViewString(p), "_tprep.g"));
    for qgens in Qgenss do
        qsigma := qgens[1];
        qtau := qgens[2];
        for aut in cok_reps do
            for tau in PreImages(epi, Image(aut, qtau)) do
                if GcdInt(Order(tau), p) <> 1 then
                    continue;
                fi;
                for sigma in PreImages(epi, Image(aut, qsigma)) do
                    if tau^sigma <> tau^p then
                        continue;
                    fi;
                    return [sigma, tau];
                od;
            od;
        od;
    od;
    return fail;
end;

LiftGenss := function(label, p)
    local qgens, qsigma, qtau, qx0, qx1, sigma, tau, x0, x1, aut, genss, V, h2, abelian_pcore, phiGV, tame_size, Gsize, qsigmas, slookup, qtaus, stlookup, qx1s, stxlookup, qx0s, sigmas, taus, x1s, x0s, orbstab, sorbit, sstab, torbit, tstab, x1orbit, x1stab, x0orbit, phiGVsigma, x, x1rel, x0rel;

    # The prep file provides the global variables
    # G -- the group corresponding to label
    # epi -- the epimorphism to the chosen quotient Q = G/N
    # Qgenss -- a list of four-tuples giving the possible images of sigma, tau, x0, x1 in Q, up to automorphism
    # A -- Aut(G)
    # ischarsub -- whether N is a characteristic subgroup
    # Let AA be the subgroup of A that stabilizes N (so A = AA when N is characteristic)
    # cok_reps -- a list of automorphisms of Q representing the cosets of the image of AA in Aut(Q)
    # ker_reps -- ker(AA -> Aut(Q))
    ##### The file also provides technical variables used in the computation of the relation
    # ppartGExp -- the p-part of the exponent of G
    # projp -- an integer m so that raising to the mth power projects every element of G onto its p-primary part
    # proj2 -- an integer m so that raising to the mth power projects every element of G onto its 2-primary part
    # h -- an integer that is a (p-1)st root of unity modulo the p-part of the exponent of G.
    Read(Concatenation("IGPdata/", label, "_", ViewString(p), "_prep.g"));

    h2 := PowerModInt(h, proj2, ppartGExp);
    V := PCore(G, p);
    phiGV := NaturalHomomorphismByNormalSubgroupNC(G, V);
    tame_size := Size(Image(phiGV));
    Gsize := Size(G);
    abelian_pcore := IsAbelian(V);
    genss := [];
    qsigmas := [];
    slookup := NewDictionary(One(G), false);
    qtaus := NewDictionary(One(G), true);
    stlookup := NewDictionary([One(G),One(G)],false);
    qx1s := NewDictionary([One(G),One(G)],true);
    stxlookup := NewDictionary([One(G),One(G),One(G)],false);
    qx0s := NewDictionary([One(G),One(G),One(G)],true);
    for qgens in Qgenss do
        for aut in cok_reps do
            qsigma := Image(aut, qgens[1]);
            qtau := Image(aut, qgens[2]);
            qx0 := Image(aut, qgens[3]);
            qx1 := Image(aut, qgens[4]);
            if not KnowsDictionary(slookup, qsigma) then
                Append(qsigmas, [qsigma]);
                AddDictionary(slookup, qsigma);
                AddDictionary(qtaus, qsigma, []);
            fi;
            if not KnowsDictionary(stlookup, [qsigma, qtau]) then
                AddDictionary(stlookup, [qsigma, qtau]);
                AddDictionary(qx1s, [qsigma, qtau], []);
            fi;
            if not KnowsDictionary(stxlookup, [qsigma, qtau, qx1]) then
                AddDictionary(stxlookup, [qsigma, qtau, qx1]); #change order since x1 relation more complicated
                AddDictionary(qx0s, [qsigma, qtau, qx1], []);
            fi;
            Append(LookupDictionary(qtaus, qsigma), [qtau]);
            Append(LookupDictionary(qx1s, [qsigma, qtau]), [qx1]);
            Append(LookupDictionary(qx0s, [qsigma, qtau, qx1]), [qx0]);
        od;
    od;
    sigmas := Set([]);
    for qsigma in qsigmas do
        UniteSet(sigmas, List(PreImages(epi, qsigma)));
    od;
    while Length(sigmas) > 0 do
        Print("sigmas ", sigmas, "\n");
        sigma := sigmas[1];
        qsigma := Image(epi, sigma);
        orbstab := OrbitStabilizer(A, sigma);
        sorbit := orbstab.orbit;
        sstab := orbstab.stabilizer;
        phiGVsigma := Image(phiGV, sigma);
        taus := Set([]);
        for qtau in LookupDictionary(qtaus, qsigma) do
            UniteSet(taus, Filtered(PreImages(epi, qtau), x-> (GcdInt(Order(x), p) = 1 and
                                                               x^sigma = x^p and
                                                               Size(Group(phiGVsigma,Image(phiGV,x))) = tame_size)));
        od;
        while Length(taus) > 0 do
            Print("taus ", taus, "\n");
            tau := taus[1];
            qtau := Image(epi, tau);
            orbstab := OrbitStabilizer(sstab, tau);
            torbit := orbstab.orbit;
            tstab := orbstab.stabilizer;
            x1s := Set([]);
            for qx1 in LookupDictionary(qx1s, [qsigma, qtau]) do
                UniteSet(x1s, Filtered(PreImages(epi, qx1), x -> x in V));
            od;
            while Length(x1s) > 0 do
                Print("x1s ", x1s, "\n");
                x1 := x1s[1];
                qx1 := Image(epi, x1);
                x1rel := false; # might not need to compute
                orbstab := OrbitStabilizer(tstab, x1);
                x1orbit := orbstab.orbit;
                Print("x1orbit", x1orbit, "\n");
                x1stab := orbstab.stabilizer;
                x0s := Set([]);
                for qx0 in LookupDictionary(qx0s, [qsigma, qtau, qx1]) do
                    UniteSet(x0s, Filtered(PreImages(epi, qx0), x -> (x in V and Size(Subgroup(G,[sigma, tau, x, x1]))=Gsize)));
                od;
                while Length(x0s) > 0 do
                    Print("x0s ", x0s, "\n");
                    if x1rel = false then
                        x1rel := X1Relation(sigma, tau, x1, p, h2, projp, proj2, ppartGExp, abelian_pcore);
                    fi;
                    x0 := x0s[1];
                    x0orbit := Orbit(x1stab, x0);
                    x0rel := X0Relation(sigma, tau, x0, p, h, projp);
                    if x0rel = x1rel then
                        Print("Success ", [sigma, tau, x0, x1], "\n");
                        Append(genss, [[sigma, tau, x0, x1]]);
                    fi;
                    SubtractSet(x0s, x0orbit);
                od;
                SubtractSet(x1s, x1orbit);
            od;
            SubtractSet(taus, torbit);
        od;
        SubtractSet(sigmas, sorbit);
    od;
    Print("***********************\n");
    for orbstab in Orbits(A, genss, OnTuples) do
        Print(List(orbstab), "\n");
    od;
    PrintTo(Concatenation("IGPdata/", label, "_", ViewString(p), "_genss.g"), genss);
    return Length(genss);
    #return genss;
end;

GENSS_LOADED := function()
    return 1;
end;
