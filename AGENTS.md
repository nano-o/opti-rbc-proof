# AGENTS.md

In this project, we are developing a specification and proof of safety and liveness, in Isabelle/HOL, of the algorithm in described in Optimistic_RBC.pdf

The specification is in OptiRBC/OptiRBC.thy

## Instructions

- Only access Isabelle theory files using the Isabelle IQ MCP server. Do not update them in any other way. Do not write theory files directly, use the Isabelle MCP server. If a theory file is not accessible through IQ because of sandboxing rules, you may read it through other means; but do not write to it.
- Make sure that definitions and lemma do not depend on the state or messages of Byzantine parties, as these can be arbitrary.
- Try to not use small standalone helper lemmas outside main lemmas. Thanks to Isar, these can be stated inside the proof of the main lemmas.
- When checking whether a proof is complete, always check both for errors and for commands that might still be processing. If a proof methods runs for more that 3 seconds, consider that a failure and terminate it.
- Always use UTF-8-Isabelle encoding when writing to theory files.
- Do not try to use any REPL
- When working on a proof (be it a top-level lemma or a sub-proof in a structure Isar proof), first write a proof sketch in English as a comment right after stating what you are trying to prove. 
- Don't use reserved keywords like "prop" or "term" to name a fact.
- The user might chose to import the theory `Timed_Methods.thy`. This theory wraps common methods (`auto`, `simp`, `simp_all`, `blast`, `metis`) to enforce short timeouts. The wrappers emit warnings like `auto: timeout`, `simp: timeout`, or `blast: timeout`; treat those warnings as the signal that the method failed due to a timeout, not because the proof step is invalid.
- Do not use `(* ... *)` comments in theory files; prefer `text ‹...›` so notes appear in the typeset document.
- When writing comments, use term antiquotations `@{term "..."}` (don't use "prop"). Math symbols or even names with underscores, if outside antiquotations, will cause latex failures during document processing.
- When addressing Isabelle warnings, fix ones with a clear one-line change, and leave any that require more than a one-line adjustment.
- Before considering a task complete, use `isabelle build` to check that everything builds properly.
  Also make sure the proof sketches for any newly completed proof are still accurate.
- If needed, you can find Isabelle documentation PDF files somewhere in the Isabelle distribution
- Note that the IQ method `write_file` does not write to disk but only update the file as it's loaded in Isabelle/jEdit. Use `save_file` to write to disk.
- In proofs, when some established or assumed propositions are no too long, avoid creating names for them and instead use `‹...›`
- When a type is of type class `finite`, no need to prove that sets of elements of this type are finite. The simplifier and other proof methods can derive that on their own.
- To run sledgehammer on a goal without a REPL, use `mcp__iq__explore` with `query="sledgehammer"`. The pattern must identify the **proposition statement** (e.g., `have f_pos: "f ≥ 1"`), NOT the existing proof-method line (e.g., `by auto`). The tool runs sledgehammer on the goal **after** the anchor command, so anchoring on the `by` line would target the wrong proof state. Leave the `arguments` field empty (do not pass it) to use the default provers and timeout; passing anything other than prover names in `arguments` breaks the query. Do not run more that 2 sledgehammer queries in parallel.

### Encoding note for theory files:
- Full file recreationg/overwrite can cause Isabelle/JEdit to reset the endoding
  to plain `UTF-8` which, once the file is saved with that encoding, will cause
  batch operations to fail with `Malformed command syntax`.
- So, prefer small in-place edits via iq (`write_file`) and avoid full file
  recreation/overwrite of theory files unless explicitly requested.
- If `isabelle build` reports malformed syntax on otherwise normal lines (often
  near symbols/cartouches), notify the user to reset the buffer encoding in
  Isabelle/JEdit to `UTF-8-Isabelle` and save the file.
