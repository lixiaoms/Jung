# Files to publish

Use the contents of this directory as the root of the GitHub repository.
Preserve the relative directory layout and include the two dotfiles.

Publish all of the following together:

- Jung/ and Jung5/: all 25 proof modules, including the exact certificate data;
- Jung.lean and Jung5.lean: the two library entry points;
- Audit.lean: the theorem-statement and foundational-dependency audit;
- lakefile.lean, lean-toolchain, and lake-manifest.json: the pinned build;
- verify.py: the source-integrity, build, and audit checker;
- README.md, BUILD.md, PROOF_GUIDE.md, and this file: English documentation;
- CITATION.cff: citation metadata;
- verification/: the public audit, source hashes, verification summary, and
  explanation;
- release_manifest.json: the distribution file inventory and SHA-256 digests;
- .gitignore and .gitattributes: generated-file exclusions and byte preservation.

Publishing only the two Main.lean files is insufficient: their imported proof
modules and certificate data are required to compile the results.

Build outputs and downloaded dependencies are recreated by Lake. They are not
part of the source distribution and are excluded by .gitignore.

Before citing the repository in the article, identify the Git commit or release
tag containing the checked proof. CITATION.cff provides the author and software
title without requiring a repository URL in advance.
