# Prover9/Mace4 inputs for E677 conjugation lemmas
Binaries: ~/ladr/provers.src/prover9 , ~/ladr/mace4.src/mace4 (rebuild: ~/ladr/REBUILD.sh)

- dL.in        : deg_L<=1 (left-fixer/conjugation uniqueness from z-side). E677+left-QG. PROVED (24 steps).
- dR.in / dRs.in : deg_R<=1 (conjugator uniqueness, conjugation & S forms). E677+left-QG. SEARCH FAILED.
- dR_fullqg.in : deg_R<=1 from E677+FULL quasigroup. PROVED (12 steps) -- just right-cancellation.
- dR_hard.in   : deg_R<=1, E677+left-QG, auto2/300s/+left-div lemma. SEARCH FAILED.
- dRcex.in     : Mace4 search for a counterexample to deg_R<=1 (E677 + two distinct conjugators). None found (timed out).

Summary: deg_R<=1 is provable for quasigroup E677 magmas (right-cancellation) but OPEN for
non-right-cancellative ones (e.g. 77/65) -- mirrors the E677|=fin E255 hard case (non-QG).
deg_R>=1 (existence) is equivalent to E255 itself.

- s2u.in       : slice-2 uniqueness z*(x*(x*x))=x & w*(...)=x -> z=w. E677+left-QG. SEARCH FAILED.
- s2u_qg.in    : same from E677+full-QG. PROVED (8 steps, right-cancellation).
- s2u_cex.in   : Mace4 counterexample search. None found n<=12.
