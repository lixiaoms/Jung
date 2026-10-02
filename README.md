# Lean formalization of the ambient Jung bound in dimensions 4k+1

This repository accompanies *An upper bound for the ambient Jung constant of
$\ell_1^{4k+1}$* by Xiao Li. It proves the ambient enclosing-radius upper
bound for every integer $k\ge 1$, including arbitrary nonempty sets of real
points. It also contains a verified four-point sharpness example in dimension
five.

## Main theorem

For every natural number k >= 1, every nonempty set of points in real
l1^(4k+1), and every D >= 0, if all pairwise Manhattan distances are at most D,
there exists a real ambient center whose distance from every point is at most
((4k - 1) / (4k)) * D.

The complete public Lean statement is:

~~~lean
theorem jung_l1_four_k_plus_one_explicit (k : ℕ) (hk : 1 ≤ k)
    (X : Set (Fin (4*k+1) → ℝ)) (hne : X.Nonempty) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x∈X,∀ y∈X,(∑ j : Fin (4*k+1),|x j-y j|) ≤ D) :
    ∃ c : Fin (4*k+1) → ℝ,∀ x∈X,
      (∑ j : Fin (4*k+1),|x j-c j|) ≤ ((4*(k:ℝ)-1)/(4*(k:ℝ)))*D
~~~

The entry point is [Jung/Main.lean](Jung/Main.lean). The result includes infinite
sets, repeated points, tied coordinate values, and D = 0. Its center is
unrestricted in the original real ambient space. No contact, sorting, or cut
representation assumption is added to the public theorem.

## Five-dimensional case

[Jung5/Main.lean](Jung5/Main.lean) contains:

- Jung5.jung_l1_five_explicit: the enclosing-radius upper bound 3D/4 for every
  nonempty set of real five-dimensional points.
- Jung5.jung_l1_five_sharp: a four-point set of diameter one, with radius exactly
  3/4 for unrestricted ambient centers.

Together these establish the sharp ambient Jung value 3/4 in dimension five.

## Build and audit

The project pins Lean 4.34.0 and mathlib commit
5ed2965256430c3649e86755f9576b54eca72435. Install Lean through elan and run these
commands from the repository root:

~~~sh
lake exe cache get
python3 verify.py
~~~

The verifier checks source integrity, builds both proof libraries, runs
Audit.lean, and checks the complete set of 151 foundational-dependency reports.
The accepted foundations are propext, Classical.choice, and Quot.sound.

For manual commands, prerequisites, and an integrity-only check, see
[BUILD.md](BUILD.md). For a step-by-step account of the mathematics, see
[PROOF_GUIDE.md](PROOF_GUIDE.md). The archived audit and its scope are documented
in [verification/VERIFICATION.md](verification/VERIFICATION.md).

## Repository contents

| Path | Purpose |
|---|---|
| Jung/ | General-dimensional proof modules and the unified k >= 1 theorem |
| Jung5/ | Complete five-dimensional proof, exact certificate data, and sharpness |
| Jung.lean, Jung5.lean | Library entry points for import Jung and import Jung5 |
| Audit.lean | Explicit theorem statements and 151 transitive axiom reports |
| lakefile.lean | Lake package and proof-library definitions |
| lean-toolchain | Exact Lean toolchain selection |
| lake-manifest.json | Locked direct and transitive dependency revisions |
| verify.py | Source-integrity, build, and axiom-audit checker |
| verification/ | Public theorem audit, source hashes, and verification summary |
| CITATION.cff | Citation metadata |

## Formalization scope

The formalized claims are the upper bound for every k >= 1 and the explicit
five-dimensional sharpness witness. The general Hadamard construction,
Sylvester recursion, and further plateau equalities in the article are not
separate formalized theorems in this repository. The project does not prove an
equilateral-set cardinality bound or the remaining 4k+2 plateau case.

When citing the formalization, identify the repository commit or a release tag
so the exact proof sources and dependency lock are recoverable.
