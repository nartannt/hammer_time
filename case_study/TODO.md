
# Plan

Have 4 files, 2 lean and 2 isabelle, the first two files will be parallel formalisations of conrete semantics with no automation. The second two files will attempt to automate the proof files as much as possible using sledgehammer and the lean hammer.

# DONE

    - copy isabelle files from relevant concrete semantics snippet

# DOING
    
    - translating isabelle files into lean

# TODO

## Fix
    
    - check with Xavier if it can be possible to have equality in the program equivalence definition

## Check

    - if using a schematic variable notation similar to Isabelle is possible
    - if it's reasonable to have a list like notation for sequences of state modifications s[x↦1, y↦2] instead of s[x↦1][y↦2]
    - is there a way to remove the quotPrecheck deactivation

## Unautomated parallel files

    - get isabelle to build (waiting on isabelle vampire patch in nix packages)
    - check that the copied isabelle files compile
    - clean up lean file (make proofs nice)

## Automated parallel files

    - replace as many of the proofs as possible by sledgehammer calls in copies (isabelle)
    - replace as many of the proofs as possible by hammer calls in copies (lean)
