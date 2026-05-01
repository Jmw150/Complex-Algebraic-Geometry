###############################################################################
# Q1.5 counterexample search — PSL(2, p) families.
#
# Scans G = PSL(2, p) for primes p in a specified list.
# Looks for core-free, Q-coset equivalent, non-isomorphic subgroup pairs.
#
# KLMRS Question 1.5 (arXiv:2602.15463v1, Feb 2026):
#   Are two core-free Z-coset equivalent subgroups always isomorphic?
#
# Scott's pair lives in PSL(2,29) and is the only known non-conjugate
# Z-coset equivalent pair.  That pair is isomorphic; we hunt for a
# non-isomorphic one.
#
# Output: one JSON line per candidate, plus progress/summary comments.
#
# Run:
#   gap -q -b tools/cag_gap/q15_search_psl.g
###############################################################################

# ---- Shared predicate definitions ----------------------------------------

# Core-free predicate.
IsCoreFreeSub := function(G, H)
    return Size(Core(G, H)) = 1;
end;

# Q-coset equivalence (Gassmann-Sunada): equal permutation characters.
IsQCosetEquivalent := function(G, H1, H2)
    return PermutationCharacter(G, H1) = PermutationCharacter(G, H2);
end;

# Element-order multiset fast pre-filter.
ElementOrderMultiset := function(H)
    return SortedList(List(Elements(H), Order));
end;

IsElementOrderEquiv := function(H1, H2)
    return ElementOrderMultiset(H1) = ElementOrderMultiset(H2);
end;

# Z-coset equivalence via Burnside table-of-marks criterion.
# Falls back to permutation-character equality if TOM lookup fails.
IsZCosetEquivalent := function(G, H1, H2)
    local tom, c1, c2;
    tom := TableOfMarks(G);
    c1 := First([1..Length(OrdersTom(tom))], i ->
        Order(RepresentativeTom(tom, i)) = Size(H1) and
        IsConjugate(G, RepresentativeTom(tom, i), H1));
    c2 := First([1..Length(OrdersTom(tom))], i ->
        Order(RepresentativeTom(tom, i)) = Size(H2) and
        IsConjugate(G, RepresentativeTom(tom, i), H2));
    if c1 = fail or c2 = fail then
        return PermutationCharacter(G, H1) = PermutationCharacter(G, H2);
    fi;
    return MarksTom(tom)[c1] = MarksTom(tom)[c2];
end;

# (P2) Dedekind: every subgroup is normal.
IsDedekindGroup := function(G)
    return ForAll(ConjugacyClassesSubgroups(G),
                  c -> IsNormal(G, Representative(c)));
end;

# (P3) Every core-free subgroup of G is abelian.
AllCoreFreeAbelian := function(G)
    local reps;
    reps := List(ConjugacyClassesSubgroups(G), Representative);
    return ForAll(reps,
                  H -> not IsCoreFreeSub(G, H) or IsAbelian(H));
end;

# Combined "covered by proven theorems" check.
IsCoveredByProvenTheorems := function(G)
    if IsAbelian(G) then return true; fi;
    if IsDedekindGroup(G) then return true; fi;
    if AllCoreFreeAbelian(G) then return true; fi;
    return false;
end;

# ---- Scanner for a single group G with a label string --------------------

ScanGroup := function(G, family_label)
    local classes, reps, j, k, A, B, candidates, n_pairs;
    candidates := [];
    n_pairs := 0;
    if IsCoveredByProvenTheorems(G) then
        Print("# ", family_label, " covered by proven theorems, skipping\n");
        return rec(pairs := 0, candidates := []);
    fi;
    classes := ConjugacyClassesSubgroups(G);
    reps := List(classes, Representative);
    Print("# ", family_label, " |G|=", Size(G),
          " conjugacy classes of subgroups: ", Length(reps), "\n");
    for j in [1..Length(reps)] do
        for k in [j+1..Length(reps)] do
            A := reps[j];
            B := reps[k];
            if Size(A) <> Size(B) then continue; fi;
            if Size(A) = 1 or Size(A) = Size(G) then continue; fi;
            if not IsCoreFreeSub(G, A) then continue; fi;
            if not IsCoreFreeSub(G, B) then continue; fi;
            n_pairs := n_pairs + 1;
            if not IsElementOrderEquiv(A, B) then continue; fi;
            if not IsQCosetEquivalent(G, A, B) then continue; fi;
            if IsomorphismGroups(A, B) <> fail then continue; fi;
            # Strong candidate: Q-coset equivalent, non-isomorphic, core-free.
            Print("{\"family\":\"", family_label, "\"",
                  ",\"size\":", Size(G),
                  ",\"sub_size\":", Size(A),
                  ",\"i\":", j,
                  ",\"j\":", k,
                  ",\"iso\":false",
                  ",\"q_equiv\":true",
                  ",\"z_equiv\":", IsZCosetEquivalent(G, A, B),
                  "}\n");
            Add(candidates, [family_label, j, k]);
        od;
    od;
    return rec(pairs := n_pairs, candidates := candidates);
end;

# ---- Main: iterate over PSL(2, p) ----------------------------------------

PRIMES_TO_SCAN := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

total_pairs := 0;
total_candidates := 0;
G_main := fail;
label_main := "";
res_main := fail;
p_main := 0;

Print("# Q1.5 PSL(2,p) search — primes: ", PRIMES_TO_SCAN, "\n");

for p_main in PRIMES_TO_SCAN do
    label_main := Concatenation("PSL(2,", String(p_main), ")");
    Print("# constructing ", label_main, " ...\n");
    G_main := PSL(2, p_main);
    res_main := ScanGroup(G_main, label_main);
    total_pairs := total_pairs + res_main.pairs;
    total_candidates := total_candidates + Length(res_main.candidates);
    Print("# ", label_main, " done: ", res_main.pairs, " pairs checked, ",
          Length(res_main.candidates), " candidates\n");
od;

Print("# ===\n");
Print("# PSL(2,p) search complete.\n");
Print("# Total subgroup pairs examined: ", total_pairs, "\n");
Print("# Total candidates found: ", total_candidates, "\n");

QUIT;
