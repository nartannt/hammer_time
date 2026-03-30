# TODO

    - find title for paper
        + Nailing the Basics with LeanHammer
        + Sharpening LeanHammer
        + Optimising LeanHammer

    - investigate LeanHammer
        + failure rate
        + speed
    
    - possible reasons for slowness / failure
        + missing lemmas / premise selector
        + reconstruction
        + time slicing
        + Zippperposition call (not using portfolio mode)
        + not using other provers (Vampire ...) (note that the Vampire support for HOL is not stable yet)


# Observations and things to figure out

    - current invocations of zipperposition don't seem to be able to handle more than a few dozen lemmas
    - the tptp file seems to be missing lemmas that the hammer should be translating (is this the translation silently failing?)



# Working on

## Tanguy

    - finishing to fix and lint lean project
    - investigate how to make tptp files human readable or at least more so
    - look into transformation of tptp files to simplify strange encodings 
    - Lean-Auto expects lemmas / props for inductive definitions to be manually passed when used in conjunction with atps: does LH (or its premise selector) try to do this? or is this the reason that we always have to manually add the inductive definition lemmas when calling `hammer`?

## Xavier

    - investigate Isabelle invocations
    - PR / issue for different (ie. Isabelle-like) options for zipperposition 

## Jasmin

# Questions

## For Jasmin
    
    - how many lemmas / facts does Isabelle send to its provers and zipperposition in particular
    - what are possible reasons that zipp only seems to be able to handle so few lemmas in the lean case

