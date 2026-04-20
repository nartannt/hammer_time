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
    - look into transformation of tptp files to simplify strange encodings 
    - investigate if it's possible to manipulate the LA monomorphisation procedure to prioritise certain lemmas and if not have some kind of feedback on the lemmas whose translation failed or couldn't be done in time

## Xavier

    - investigate Isabelle invocations
        - Do a side by side of natural number game.
    - PR / issue for different (ie. Isabelle-like) options for zipperposition 

## Jasmin

# Questions

## For Jasmin
    
    - how many lemmas / facts does Isabelle send to its provers and zipperposition in particular


# Issues

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

    - with an empty or almost empty context, the premise selector will start suggesting nonsense lemmas. This is to be expected, however if the number of allowed premises isn't very low, there's a good chance that the premise selector will chose some random lemmas which, when taken together, cause the translation to fail for some of these lemmas.
