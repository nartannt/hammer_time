
# Plan

Have 4 files, 2 lean and 2 isabelle, the first two files will be parallel formalisations of conrete semantics with no automation. The second two files will attempt to automate the proof files as much as possible using sledgehammer and the lean hammer.

# DONE

    - copy isabelle files from relevant concrete semantics snippet

# TODO

## Unautomated parallel files

    - get isabelle to build (waiting on vampire patch in nix packages)
    - check that the copied isabelle files compile
    - finish translating isabelle files into lean
    - remove automation from isabelle and lean files

## Automated parallel files

    - replace as many of the proofs as possible by sledgehammer calls in copies (isabelle)
    - replace as many of the proofs as possible by hammer calls in copies (lean)
