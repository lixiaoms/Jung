# Verification evidence

The public theorem statements and all 151 foundational-dependency reports are
in [audit.log](audit.log). The source hashes are in
[source_manifest.json](source_manifest.json).

The audit includes the upper bound for every k >= 1, the five-dimensional
upper bound for arbitrary nonempty real sets, and the explicit four-point
sharpness witness. Every reported dependency is one of:

- propext;
- Classical.choice;
- Quot.sound.

The proof modules use no sorry or admit placeholders, no added mathematical
axiom declarations, and no native_decide certificates. The finite
five-dimensional certificate is checked by exact reduction in the Lean
kernel.

[summary.json](summary.json) records the checked versions, proof-module count,
audited theorem count, allowed foundations, and formalization scope. The
committed source manifest covers every proof/audit source and the pinned
build configuration. It contains only repository-relative file names,
byte sizes, and SHA-256 digests.

Run python3 verify.py to build the project and check a new audit. Running
python3 verify.py --check-only checks the distributed hashes and archived
audit without recompiling the proof. Full instructions are in
[BUILD.md](../BUILD.md).

The Hadamard construction, Sylvester recursion, and general plateau equality
corollaries in the article are outside the separately formalized scope. The
upper bound for every k >= 1 and the five-dimensional sharpness example are
included.
