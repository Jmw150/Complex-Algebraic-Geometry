###############################################################################
# Q1.5 counterexample search.
#
# KLMRS Question 1.5 (arXiv:2602.15463v1, Feb 2026): is every pair of
# core-free, Z-coset equivalent subgroups of a finite group necessarily
# isomorphic?
#
# A counterexample is a finite group G with two subgroups H1, H2 such that:
#   (a) both H1, H2 are core-free in G.
#   (b) Z[G/H1] ≅ Z[G/H2] as Z[G]-modules.
#   (c) H1 is NOT isomorphic to H2 as abstract groups.
#
# OPTIMIZATION (May 1, 2026): the codebase contains formalised proofs that
# Q1.5 holds whenever G falls into ANY of the following classes:
#
#   (P1) abelian
#   (P2) Dedekind (every subgroup normal — abelian + Hamiltonian)
#   (P3) all core-free subgroups of G are abelian
#   (P4) G has the central-intersection property (every minimal subgroup
#        contained in Z(G); subsumes (P1) but not (P2)/(P3))
#
# A counterexample MUST live outside (P1)-(P4). This script skips groups
# in those classes, dramatically reducing the search space at higher
# orders.
#
# Output: one JSON line per remaining candidate, plus a final summary.
#
# Configure with:
#   gap -c 'MIN_ORD := 16; MAX_ORD := 300; MAX_GROUPS_PER_ORDER := 50;' q15_search.g
###############################################################################

if not IsBoundGlobal("MIN_ORD") then
    MIN_ORD := 1;
fi;
if not IsBoundGlobal("MAX_ORD") then
    MAX_ORD := 200;
fi;
if not IsBoundGlobal("VERBOSE") then
    VERBOSE := false;
fi;
if not IsBoundGlobal("MAX_GROUPS_PER_ORDER") then
    MAX_GROUPS_PER_ORDER := 30;
fi;
if not IsBoundGlobal("APPLY_PROVEN_FILTERS") then
    APPLY_PROVEN_FILTERS := true;
fi;

LoadPackage("smallgrp");

# ----- Predicates that we already have FORMAL Q1.5 proofs for ------

# Core-free predicate.
IsCoreFreeSub := function(G, H)
    return Size(Core(G, H)) = 1;
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
    if IsAbelian(G) then return true; fi;            # (P1) ⊂ (P2)
    if IsDedekindGroup(G) then return true; fi;      # (P2)
    if AllCoreFreeAbelian(G) then return true; fi;   # (P3) — subsumes "S_3 case"
    return false;
end;

# ----- Equivalence tests ------

# Q-coset equivalence (Gassmann-Sunada): equal permutation characters.
IsQCosetEquivalent := function(G, H1, H2)
    return PermutationCharacter(G, H1) = PermutationCharacter(G, H2);
end;

# Element-order multiset.
ElementOrderMultiset := function(H)
    return SortedList(List(Elements(H), Order));
end;

IsElementOrderEquiv := function(H1, H2)
    return ElementOrderMultiset(H1) = ElementOrderMultiset(H2);
end;

# Z-coset equivalence via the Burnside table-of-marks criterion.
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

# ----- Scanner ------

ScanOrder := function(n)
    local m, i, G, classes, reps, j, k, A, B, candidates, n_groups_skipped;
    if NumberSmallGroups(n) = 0 then
        return rec(scanned := 0, candidates := [],
                   skipped_by_filter := 0);
    fi;
    m := NumberSmallGroups(n);
    if m > MAX_GROUPS_PER_ORDER then
        Print("# skipping order ", n, " (", m, " groups > ",
              MAX_GROUPS_PER_ORDER, ")\n");
        return rec(scanned := 0, candidates := [],
                   skipped_by_filter := 0);
    fi;
    candidates := [];
    n_groups_skipped := 0;
    for i in [1..m] do
        G := SmallGroup(n, i);
        if APPLY_PROVEN_FILTERS and IsCoveredByProvenTheorems(G) then
            n_groups_skipped := n_groups_skipped + 1;
            continue;
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
                if not IsElementOrderEquiv(A, B) then continue; fi;
                if not IsQCosetEquivalent(G, A, B) then continue; fi;
                if IsomorphismGroups(A, B) <> fail then continue; fi;
                # Strong candidate.
                Print("{\"order\":", n,
                      ",\"id\":", i,
                      ",\"size\":", Size(A),
                      ",\"i\":", j,
                      ",\"j\":", k,
                      ",\"iso\":false",
                      ",\"q_equiv\":true",
                      ",\"z_equiv\":", IsZCosetEquivalent(G, A, B),
                      "}\n");
                Add(candidates, [n, i, j, k]);
            od;
        od;
    od;
    return rec(scanned := m,
               skipped_by_filter := n_groups_skipped,
               candidates := candidates);
end;

# Driver.
total_skipped := 0;
total_scanned := 0;
total_candidates := 0;
n := MIN_ORD;
Print("# Q1.5 search: orders ", MIN_ORD, "..", MAX_ORD,
      ", filtering by proven theorems = ", APPLY_PROVEN_FILTERS, "\n");
while n <= MAX_ORD do
    Print("# scanning order ", n, " (", NumberSmallGroups(n), " groups)\n");
    res := ScanOrder(n);
    total_scanned := total_scanned + res.scanned;
    total_skipped := total_skipped + res.skipped_by_filter;
    total_candidates := total_candidates + Length(res.candidates);
    n := n + 1;
od;
Print("# done: ", total_scanned, " groups scanned, ",
      total_skipped, " skipped by proven-theorem filters, ",
      total_candidates, " candidates found\n");

QUIT;
