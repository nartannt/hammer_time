
# Plan

Have 4 files, 2 lean and 2 isabelle, the first two files will be parallel formalisations of conrete semantics with no automation. The second two files will attempt to automate the proof files as much as possible using sledgehammer and the lean hammer.

# DONE

    - copy isabelle files from relevant concrete semantics snippet

# DOING
    
    - translating isabelle files into lean
        x BigStep
        - SmallStep

# TODO

    - change lean files into proper project 

## Fix
    
    - import modules / libraries correctly in lean project

## Check

    - if using a schematic variable notation similar to Isabelle is possible
    - is there a way to remove the quotPrecheck deactivation

## Unautomated parallel files

    - get isabelle to build (waiting on isabelle vampire patch in nix packages)
    - check that the copied isabelle files compile
    - clean up lean proofs

## Automated parallel files

    - replace as many of the proofs as possible by sledgehammer calls in copies (isabelle)
    - replace as many of the proofs as possible by hammer calls in copies (lean)
