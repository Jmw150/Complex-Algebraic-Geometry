###############################################################################
# Verify Scott's example in PSL(2, 29).
#
# KLMRS arXiv:2602.15463v1, §1.2: Scott (1993) found a pair of non-conjugate
# subgroups (G1, G2) of G = PSL(2, 29) of index 203, both isomorphic to A_5,
# that are Z-coset equivalent. This script confirms the basic facts.
###############################################################################

LoadPackage("smallgrp");

G := PSL(2, 29);
Print("G = PSL(2,29), |G| = ", Size(G), "\n");

# A_5 subgroups of PSL(2,29). A_5 has order 60 so the index is 12180/60 = 203.
A5_subs := List(Filtered(ConjugacyClassesSubgroups(G),
                        c -> Size(Representative(c)) = 60),
                Representative);
Print("# of conjugacy classes of order-60 subgroups: ",
      Length(A5_subs), "\n");

# Filter to those isomorphic to A_5.
a5_iso := List(A5_subs, H -> StructureDescription(H));
Print("# structure descriptions: ", a5_iso, "\n");

# Check pairwise: are two A_5 subgroups conjugate? Q-coset equivalent?
if Length(A5_subs) >= 2 then
    H1 := A5_subs[1];
    H2 := A5_subs[2];
    Print("Pair (H1, H2):\n");
    Print("  conjugate?     : ", IsConjugate(G, H1, H2), "\n");
    Print("  Q-coset equiv? : ",
          PermutationCharacter(G, H1) = PermutationCharacter(G, H2), "\n");
    Print("  H1 ≅ H2?       : ", IsomorphismGroups(H1, H2) <> fail, "\n");
    Print("  H1 ≅ A_5?      : ", IsomorphismGroups(H1, AlternatingGroup(5)) <> fail, "\n");
    Print("  Core(G,H1) trivial?: ", Size(Core(G, H1)) = 1, "\n");
    Print("  Core(G,H2) trivial?: ", Size(Core(G, H2)) = 1, "\n");
fi;

QUIT;
