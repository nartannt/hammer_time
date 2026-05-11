# scripts/hammer_compare.py

Side-by-side capture of TPTP dumps and selected-premise lists from LeanHammer
and Sledgehammer for the same proof obligation. Capture only — no ATP runs.

## Adding a case

1. Drop `<Case>.lean` into `case_study/lean/CaseStudy/HammerCases/`. The file
   should contain a `theorem` whose proof ends in `by hammer`. Do **not**
   write `set_option hammer.autoPremisesDefault` or trace toggles in the
   file — those are passed via `lake env lean -D ...` so the case file is
   invariant across runs.
2. Drop `<Case>.thy` into `case_study/isabelle/cases/`. It must contain a
   `sledgehammer_params [overlord, provers = zipperposition, max_facts = 999
   (* HC_MAX_FACTS *), verbose]` line — the script regex-substitutes the
   number before `(* HC_MAX_FACTS *)` per pass — and a `sledgehammer`
   invocation on the target lemma.
3. Append the new theory to `case_study/isabelle/cases/ROOT`.
4. Append a `[[case]]` block to `scripts/tests.toml`.

## Running

```
python3 scripts/hammer_compare.py                         # all cases
python3 scripts/hammer_compare.py add_zero_succ           # filter by name
python3 scripts/hammer_compare.py --keep-tmp --only=lean  # debugging
```

Outputs land in `case_study/tptp_files/`:
- `lean_<name>_zipperposition_<N>premises.p`
- `isabelle_<name>_zipperposition_<N>sent_of_<pool_size>.p`

Each file's header lists the selector's full ranked output, with the first
`auto_premises` entries marked as sent to the ATP. Below the header is the
unmodified TPTP body the ATP would receive.

`--isabelle <path>` overrides the Isabelle binary (else `$ISABELLE_BIN`, else
`isabelle` on PATH). `--lake <path>` overrides Lake similarly.
