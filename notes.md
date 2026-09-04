# DONE
   - TODO Xavier: what you did to mepo and co
   - Bug in lean-auto: see issue #72
   - Bug in Duper: see issue #83
   - Implemented polarised MePo version with illustrative example in Lean
   - Implemented Iff theorems in MyHammer


# TODO

    - find title for paper
        + Nailing the Basics with LeanHammer
        + Sharpening LeanHammer
        + Optimising LeanHammer

    - Things to investigate
        + improving premise selector in general             -> Xavier and Tanguy on it
        + issues with monomorphisation                      -> Tanguy on it

        + interaction between PS and typeclasses            -> TODO
        + time slicing                                      -> TODO
        + Zippperposition call (not using portfolio mode)   -> TODO

        + reconstruction                                    -> doesn't seem to be a significant issue
        + not using other provers (Vampire ...)             -> other ppl working on this

    - Evaluation
        + compare: MyMePo, MePo, PolarisedMepo
        + compare: Hammer, MyHammer

# Working on

## Tanguy

   ### Active
    - opened issue #72 to fix a bug in lean-auto, monitoring, fixed in fork
    - create infrastructure for premise selector evaluation
    - investigate adding "Iterative Monomorphisation" bounds to LA monomorphisation
        + translates to TH0, update translation to TH1?
        + mess around with options, some of the defaults seem to have high levels of transparency for equality

   ### Passive
    - look into premise selection research, notably SiNe
    - finishing linting lean project
    - profile hammer to figure out why it is so slow
    - make a version of PolarisedMePo which takes into account Xavier's changes
    - fix crash from monomorphisation of incompatible lemmas when the premise selectors "run on empty", or at least transition to a soft failure

## Xavier

    - add our version of the hammer into the isabelle / lean comparison scripts
    - investigate tptp encoding 
    - investigate Isabelle invocations
        - Do a side by side of natural number game.
    - PR / issue for different (ie. Isabelle-like) options for zipperposition 

## Jasmin

# Questions

## For Jasmin
    
    - how many lemmas / facts does Isabelle send to its provers and zipperposition in particular


# Issues

## Missing lemmas

   The hammer can fail case splitting on inductive definitions, this is because contrary to Isabelle, Lean doesn't have an inbuilt generation of iff lemmas for inductive definitions. Once we add it ourselves, the hammer has access to the necessary lemmas to solve more problems. There is the issue that generating these lemmas for all inductive definitions in the context takes too long (~3.5s, ~1.5s with some basic filtering). However this is necessary if we want the premise selector to have access to these definitions, the alternatives being to have either multiple runs of the premise selector or to violate the number of lemmas limit set by the user.

## TPTP Translation

    The hammer sometimes fails to translate lemmas even when they are supplied by the user. However, these same lemmas can be successfully used when added to the proof context. See MissingLemmas.lean for a MWE.

    The generated TPTP problems are full of junk, there are many completely irrelevant lemmas, many facts are duplicated, many are tautologies, some types are defined that never occur in the actual problem. This shouldn't be much of an issue for zipperposition but is indicative of some upstream issues.

## Monomorphisation

    The monomorphisation procedure is very similar to one we had in the iterative monomorphisation paper
    It differs in two key ways:
        - The bounds are very different, I can spot the following:
            * total number of matches
            * heartbeats for unification of constants
            * heartbeats for unifications of terms
            the only which overlaps (at least in spirit) with our bounds is the total number of matches
        - It's unclear that they filter the unification by function symbol, this was the single most significant heuristic in our paper. Since on top of monomorphisation there is also a substitution of function symbols this may not be directly applicable.

## Minor

    - The translation of leamma exists_true_left to tptp by lean auto is not well-formed (it has an application X0 @ X0 with a type which doesn't allow this)
    - with an empty or almost empty context, the premise selector will start suggesting nonsense lemmas. This is to be expected, however if the number of allowed premises isn't very low, there's a good chance that the premise selector will chose some random lemmas which, when taken together, cause the translation to fail for some of these lemmas.
