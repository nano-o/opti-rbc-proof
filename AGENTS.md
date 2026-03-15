# AGENTS.md

In this project, we are developing a specification and proof of safety and liveness, in Isabelle/HOL, of the algorithm in described in Optimistic_RBC.pdf

The specification is in OptiRBC/OptiRBC.thy

## Instructions

- Only access Isabelle theory files using the Isabelle MCP server. Do not update them in any other way. Do not write theory files directly, use the Isabelle MCP server.
- Make sure that definitions and lemma do not depend on the state or messages of Byzantine parties, as these can be arbitrary.
- Try to not use small standalone helper lemmas outside main lemmas. Thanks to Isar, these can be stated inside the proof of the main lemmas.
- When checking whether a proof is complete, always check both for errors and for commands that might still be processing. If a command takes too long, consider that a failure and terminate it.
- Always use UTF-8-Isabelle encoding when writing to theory files.
- Do not try to use any REPL
