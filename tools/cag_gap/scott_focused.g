###############################################################################
# scott_focused.g
#
# Focused verification of Scott's PSL(2,29) example for KLMRS Question 1.5.
#
# Scott (1993): G = PSL(2,29) has two non-conjugate subgroups H1, H2 (both
# isomorphic to A_5, of index 203) that are Z-coset equivalent.
# KLMRS use this as the basis for Theorem 1.4.
#
# Fast path (avoids slow ConjugacyClassesSubgroups / MaximalSubgroupClassReps):
#   Use the Table of Marks for "L2(29)" from the tomlib package.
#   The TOM is precomputed and immediately gives us all 22 subgroup class orders,
#   plus actual subgroup representatives via RepresentativeTom.
#   Isomorphism testing uses IdSmallGroup (order-60 database lookup) instead of
#   the slow IsomorphismGroups for permutation groups.
#
# Checks:
#   1. PSL(2,29) has exactly TWO conjugacy classes of subgroups isomorphic to A_5.
#   2. Both A_5 subgroups are core-free in PSL(2,29).
#   3. The two A_5 subgroups have equal permutation characters (Q-coset equiv).
#   4. The two A_5 subgroups are isomorphic to each other (both ≅ A_5).
###############################################################################

Print("=== Scott PSL(2,29) Focused Verification ===\n\n");

LoadPackage("tomlib");
LoadPackage("smallgrp");

# ---- Load TOM for L2(29) = PSL(2,29) ----
t := TableOfMarks("L2(29)");
if t = fail then
    Print("FATAL: tomlib does not contain L2(29). Aborting.\n");
    Error("tomlib missing L2(29)");
fi;

G := UnderlyingGroup(t);
Print("G = PSL(2,29)\n");
Print("|G| = ", Size(G), "\n\n");

# ---- Identify subgroup classes of order 60 directly from TOM ----
orders := OrdersTom(t);
Print("TOM: ", Length(orders), " conjugacy classes of subgroups.\n");
Print("All subgroup orders: ", orders, "\n\n");

idx60 := Filtered([1..Length(orders)], i -> orders[i] = 60);
Print("Indices of order-60 classes: ", idx60, "\n");

# ---- CHECK 1: exactly two classes of order 60 ----
Print("\n--- CHECK 1: Two non-conjugate A_5-sized subgroup classes ---\n");
if Length(idx60) = 2 then
    Print("PASS: exactly 2 conjugacy classes of subgroups of order 60.\n");
else
    Print("FAIL/UNEXPECTED: found ", Length(idx60), " classes of order 60 (expected 2).\n");
fi;

# ---- Retrieve actual representatives ----
H1 := RepresentativeTom(t, idx60[1]);
H2 := RepresentativeTom(t, idx60[2]);
Print("\n|H1| = ", Size(H1), ", |H2| = ", Size(H2), "\n");
Print("[G:H1] = ", Index(G, H1), ", [G:H2] = ", Index(G, H2), "\n\n");

# Confirm H1 and H2 are not conjugate (they come from different TOM classes,
# but we verify directly).
conj := IsConjugate(G, H1, H2);
Print("IsConjugate(G, H1, H2) = ", conj, "\n");
if not conj then
    Print("GOOD: H1 and H2 are NOT conjugate (as expected from Scott).\n");
else
    Print("UNEXPECTED: H1 and H2 ARE conjugate.\n");
fi;

# ---- CHECK 2: core-free ----
Print("\n--- CHECK 2: Core-free ---\n");
c1 := Size(Core(G, H1));
c2 := Size(Core(G, H2));
Print("Core(G, H1) has order: ", c1, "\n");
Print("Core(G, H2) has order: ", c2, "\n");
if c1 = 1 and c2 = 1 then
    Print("PASS: both H1 and H2 are core-free in G.\n");
else
    Print("FAIL: at least one subgroup is not core-free.\n");
fi;

# ---- CHECK 3: equal permutation characters (Q-coset equivalence) ----
Print("\n--- CHECK 3: Equal permutation characters (Q-coset equivalence) ---\n");
chi1 := PermutationCharacter(G, H1);
chi2 := PermutationCharacter(G, H2);
chars_eq := (chi1 = chi2);
Print("chi1 values: ", ValuesOfClassFunction(chi1), "\n");
Print("chi2 values: ", ValuesOfClassFunction(chi2), "\n");
Print("chi1 = chi2 ? ", chars_eq, "\n");
if chars_eq then
    Print("PASS: permutation characters are equal (Q-coset equivalent).\n");
else
    Print("FAIL: permutation characters differ.\n");
fi;

# ---- CHECK 4: both subgroups are isomorphic to A_5 ----
# Use IdSmallGroup (fast database lookup) instead of IsomorphismGroups.
# A_5 = AlternatingGroup(5) = SmallGroup(60,5).
Print("\n--- CHECK 4: H1 ≅ H2 ≅ A_5 (via IdSmallGroup) ---\n");
id_A5 := IdSmallGroup(AlternatingGroup(5));
id1   := IdSmallGroup(H1);
id2   := IdSmallGroup(H2);
Print("SmallGroup id of A_5:  ", id_A5, "\n");
Print("SmallGroup id of H1:   ", id1, "\n");
Print("SmallGroup id of H2:   ", id2, "\n");
iso1 := (id1 = id_A5);
iso2 := (id2 = id_A5);
iso12 := (id1 = id2);
if iso1 and iso2 and iso12 then
    Print("PASS: H1 ≅ H2 ≅ A_5 (all three IDs match).\n");
else
    Print("FAIL: ID mismatch — H1=", id1, ", H2=", id2, ", A5=", id_A5, "\n");
fi;

# ---- Summary ----
Print("\n=== SUMMARY ===\n");
check1 := Length(idx60) = 2;
check2 := c1 = 1 and c2 = 1;
check3 := chars_eq;
check4 := iso1 and iso2 and iso12;
Print("CHECK 1 (two non-conjugate A_5 classes): ", check1, "\n");
Print("CHECK 2 (both core-free):                ", check2, "\n");
Print("CHECK 3 (equal permutation characters):  ", check3, "\n");
Print("CHECK 4 (H1 ≅ H2 ≅ A_5):                ", check4, "\n");
Print("\nAll checks passed? ", check1 and check2 and check3 and check4, "\n");

QUIT;
