# bitR8 moment basis — the oracle for mom_eq (frozen before any Lean computation)

Source: IntMul_KappaJainData, list bitR8 (46 (w,n_w) pairs, 749,446,467 children).
q-th entry = sum_w n_w * w^q, exact Python integers, q = 0..49.

Claim shape: `forall Q, hisToment net0P.hist 529 Q = histMomentum bitR8 529 Q`
= multiset equality of run-widths. With 46 distinct widths, moments q=0..45
pin the multiset COMPLETELY (Newton identities) — verifying those 46 integers
is a machine-checked multiset identity. Any single q is already a hard check.

Volume finding (settled): 749,446,467 runs x 3 numbers = 2,248,339,401 integers
vs ~2MB of closure on disk -> the runs are PROCEDURALLY GENERATED (genF), not
stored. A grep-able triple hunt is measured-impossible; the Lean #eval is the
one computation, this file is the one oracle.
