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


# Working on

## Tanguy

    - finishing to fix and lint lean project
    - investigate how to make tptp files human readable or at least more so
    - look into transformation of tptp files to simplify strange encodings 
    - Lean-Auto expects lemmas / props for inductive definitions to be manually passed when used in conjunction with atps: does LH (or its premise selector) try to do this? or is this the reason that we always have to manually add the inductive definition lemmas when calling `hammer`?
        - In the lean-auto paper, there is special support for inductive types in the translation.
        However :
            Currently, Lean-auto supports polymorphic, nested, and mutual inductive types when
            SMT solvers are used as the backend ATP. For other ATPs or unsupported inductive types,
            users can always manually supply the properties related to the inductive types as a workaround.
            (p.16-17)
    - investigate if it's possible to manipulate the LA monomorphisation procedure to prioritise certain lemmas and if not have some kind of feedback on the lemmas whose translation failed or couldn't be done in time

## Xavier

    - investigate Isabelle invocations
        - Do a side by side of natural number game.
    - PR / issue for different (ie. Isabelle-like) options for zipperposition 

## Jasmin

# Observations and things to figure out

    - current invocations of zipperposition don't seem to be able to handle more than a few dozen lemmas
    - the tptp file seems to be missing lemmas that the hammer should be translating (is this the translation silently failing?)
      this is likely due to the incomplete translation and monomorphisation procedure of LA and may explain why reducing the number of premises is helpful, if among 100 candidate premises 5 are necessary and that monomorphisation only runs for a set time or fuel, it is likely that at least one of the 5 premises doesn't make it through, whereas if fewer candidate premises are given, then perhaps all the necessary ones can be processed

## Translation and Equality
    
    In the LeanAuto paper, the authors seem to go to great length to ensure that definitionally equal terms in Lean are represented by equal terms in the translation. This seems to be both computationally demanding and incomplete. Given that Zipperposition is made to specifically handle equality, it seems strange that they do not simply attempt to encode these equalities in HOL rather than deal with them in the translation. Perhaps I missed the part where they do this, perhaps I missed the logical constraints which make this impossible.

    In fact handling definitional equality seems to be one of the major performance issues throughout the paper, they seem to attempt several methods to deal with this and the fact that I haven't found a mention of trying to give them to Zipperposition (by some encoding or translation) is surprising.

## Monomorphisation

    The monomorphisation procedure is very similar (ie. the same) to that of the one we had in the iterative monomorphisation paper
    It differs in two key ways:
        - The bounds are very different, I can spot the following:
            * total number of matches
            * heartbeats for unification of constants
            * heartbeats for unifications of terms
        - It's unclear that they filter the unification by function symbol, this was the most significant heuristic in our paper, this may be partly for technical reasons, they don't have to just match types but also transform the function symbols however, if it is indeed the case that they don't have some similar kind of grouping it could cause the monomorphisation procedure to be much less efficient than it could be. This point is mostly speculation.



# Questions

## For Jasmin
    
    - how many lemmas / facts does Isabelle send to its provers and zipperposition in particular
    - what are possible reasons that zipp only seems to be able to handle so few lemmas in the lean case

