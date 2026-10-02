# Building and checking the formalization

## Requirements and pinned versions

- elan, providing the Lean toolchain selected by lean-toolchain;
- Git and network access for public dependency retrieval;
- Python 3.8 or later for verify.py; no Python packages are required;
- Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b;
- mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.

The committed lake-manifest.json records the exact public Git revisions of
mathlib and its transitive dependencies. Keep this lock file when reproducing
the proof. Running lake update intentionally resolves the dependency
configuration again and may change the lock; it is not part of the locked
reproduction procedure.

## Recommended procedure

From the repository root:

~~~sh
lake exe cache get
python3 verify.py
~~~

The cache command retrieves prebuilt mathlib dependencies for their pinned
versions. The verifier checks verification/source_manifest.json, builds Jung
and Jung5, elaborates Audit.lean, and rejects unexpected or missing axiom
reports. It exits with a nonzero status if any step fails.

On systems where Python 3 is invoked as python, use python verify.py instead.

## Manual procedure

~~~sh
lake exe cache get
lake build Jung Jung5
lake env lean -j1 Audit.lean > audit.log
python3 verify.py --audit-log audit.log --check-only
~~~

The last command checks source integrity and the specified audit output.
It does not run a new Lean build. The generated audit.log is ignored by Git;
the committed audit is verification/audit.log.

## Checking the distributed source and archived audit

~~~sh
python3 verify.py --check-only
~~~

This checks every recorded proof/configuration hash and all 151 reports in the
archived audit. It does not replace recompilation in Lean.

The repository contains 25 proof modules, two library entry points, and one
audit driver. Both libraries
are built by the recommended command, even though the default Lake target also
imports the five-dimensional library through Jung.Main.

## File integrity

The .gitattributes file disables automatic line-ending conversion. This keeps
the byte-level SHA-256 values in verification/source_manifest.json stable
across Git checkouts. If you intentionally edit a proof or configuration file,
the integrity checker will require a newly verified source manifest.

The final verification claim must be based on a successful Lean build and an
audit of its actual compiled declarations. Source hashes and archived output
are supporting evidence, not substitutes for that build.
