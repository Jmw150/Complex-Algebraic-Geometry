###############################################################################
# Q1.5 counterexample search — transitive permutation groups (degree 8..16).
#
# Loads the `transgrp` package and iterates over TransitiveGroup(d, i) for
# degrees d in 8..16.  For each group, looks for core-free, Q-coset
# equivalent, non-isomorphic subgroup pairs — the same search as
# q15_search.g but targeting groups the small-groups library misses or
# where the transitive action gives a structurally distinct presentation.
#
# KLMRS Question 1.5 (arXiv:2602.15463v1, Feb 2026).
#
# Run:
#   gap -q -b tools/cag_gap/q15_search_transgrp.g
#
# Degree-16 has 1954 transitive groups; some are large.  We impose a
# per-group size cap (MAX_GROUP_SIZE) to keep runtime manageable.
###############################################################################

LoadPackage("transgrp");

# ---- Tuning knobs --------------------------------------------------------
if not IsBoundGlobal("MIN_DEGREE") then MIN_DEGREE := 8; fi;
if not IsBoundGlobal("MAX_DEGREE") then MAX_DEGREE := 16; fi;
# Skip any individual group whose order exceeds this bound.
if not IsBoundGlobal("MAX_GROUP_SIZE") then MAX_GROUP_SIZE := 50000; fi;

# ---- Shared predicate definitions ----------------------------------------

IsCoreFreeSub := function(G, H)
    return Size(Core(G, H)) = 1;
end;

IsQCosetEquivalent := function(G, H1, H2)
    return PermutationCharacter(G, H1) = PermutationCharacter(G, H2);
end;

ElementOrderMultiset := function(H)
    return SortedList(List(Elements(H), Order));
end;

IsElementOrderEquiv := function(H1, H2)
    return ElementOrderMultiset(H1) = ElementOrderMultiset(H2);
end;

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

IsDedekindGroup := function(G)
    return ForAll(ConjugacyClassesSubgroups(G),
                  c -> IsNormal(G, Representative(c)));
end;

AllCoreFreeAbelian := function(G)
    local reps;
    reps := List(ConjugacyClassesSubgroups(G), Representative);
    return ForAll(reps,
                  H -> not IsCoreFreeSub(G, H) or IsAbelian(H));
end;

IsCoveredByProvenTheorems := function(G)
    if IsAbelian(G) then return true; fi;
    if IsDedekindGroup(G) then return true; fi;
    if AllCoreFreeAbelian(G) then return true; fi;
    return false;
end;

# ---- Scanner for a single group ------------------------------------------

ScanGroup := function(G, family_label)
    local classes, reps, j, k, A, B, candidates, n_pairs;
    candidates := [];
    n_pairs := 0;
    if IsCoveredByProvenTheorems(G) then
        return rec(pairs := 0, candidates := [], skipped := true);
    fi;
    classes := ConjugacyClassesSubgroups(G);
    reps := List(classes, Representative);
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
            # Strong candidate.
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
    return rec(pairs := n_pairs, candidates := candidates, skipped := false);
end;

# ---- Main: iterate over transitive groups by degree ----------------------

total_pairs := 0;
total_candidates := 0;
total_groups_scanned := 0;
total_groups_skipped_size := 0;
total_groups_skipped_filter := 0;
nr_main := 0;
i_main := 0;
d_main := 0;
G_main := fail;
label_main := "";
res_main := fail;
gsz_main := 0;

Print("# Q1.5 transgrp search — degrees ", MIN_DEGREE, "..", MAX_DEGREE,
      ", MAX_GROUP_SIZE=", MAX_GROUP_SIZE, "\n");

for d_main in [MIN_DEGREE..MAX_DEGREE] do
    nr_main := NrTransitiveGroups(d_main);
    Print("# degree ", d_main, ": ", nr_main, " transitive groups\n");
    for i_main in [1..nr_main] do
        G_main := TransitiveGroup(d_main, i_main);
        gsz_main := Size(G_main);
        label_main := Concatenation("T(", String(d_main), ",", String(i_main), ")");
        if gsz_main > MAX_GROUP_SIZE then
            total_groups_skipped_size := total_groups_skipped_size + 1;
            continue;
        fi;
        res_main := ScanGroup(G_main, label_main);
        if res_main.skipped then
            total_groups_skipped_filter := total_groups_skipped_filter + 1;
        else
            total_groups_scanned := total_groups_scanned + 1;
            total_pairs := total_pairs + res_main.pairs;
            total_candidates := total_candidates + Length(res_main.candidates);
        fi;
    od;
    Print("# degree ", d_main, " done\n");
od;

Print("# ===\n");
Print("# transgrp search complete.\n");
Print("# Groups scanned (passed size+filter): ", total_groups_scanned, "\n");
Print("# Groups skipped (too large): ", total_groups_skipped_size, "\n");
Print("# Groups skipped (proven theorems): ", total_groups_skipped_filter, "\n");
Print("# Total subgroup pairs examined: ", total_pairs, "\n");
Print("# Total candidates found: ", total_candidates, "\n");

QUIT;
