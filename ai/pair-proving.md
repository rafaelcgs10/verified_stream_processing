# Pair-Proving Workflow

Guidelines for how the AI assistant collaborates with the user on Isabelle/HOL proofs.

Note: At the start of any session, first confirm the MCP connection to Isabelle/HOL using the `IQ_AUTH_TOKEN` environment variable.

## Roles

- The AI assistant tries to proof auxiliary lemmas asked by the user.
- The AI must try to look for counter examples, or missing/wrong assumptions for those auxiliary lemmas if they seem too hard to prove (e.g. after many atempts).

## Editing

- The AI always saves the file after editing it.
- The AI checks the region before writing the file to avoinding writing in the middle of another lemma or definition.
- The AI alawys checks the MCP connection on the start of a session. The token  MY_TOKEN (use this).
- Don't start working without a MCP connection, just report the issue if there is no MCP connection.
- **For Isabelle theory files (.thy), always edit via `mcp__isabelle__write_file`** (use `str_replace`, `insert`, or `line` command). This triggers re-processing of only the affected commands. Do NOT use the built-in `Edit`/`Write` tools on .thy files — they cause Isabelle to invalidate and re-process the entire file, which is very slow and burns time.
- Non-.thy files (e.g. markdown, scripts) can be edited normally with `Edit`/`Write`.
## Exploration

- The assistant **proactively** uses MCP tools to explore the codebase: reading definitions, looking up types, finding theorems, and running sledgehammer.
- The AI does not try to use the REPL because it does not work at the moment.
- The AI never tries to build the entire project, only uses the MCP to check the proof progress.
- However, MCP results are **hints only** -- the connection is not fully reliable. The assistant should never treat MCP output as ground truth.
- You should not look at the AFP, as there is nothing relevant there about our work.
- When asked to proof a lemma, the investigate the main definitions of the lemma, but limits the search to a certain small depth

## Proof Granularity

- The AI works on entiry proofs, but may ask question to the use at certain steps of the proof if they seem unprovable.

## Verification

- The assistant can check proof state via MCP as a first pass.
- The user does a **final verification in jEdit** for key steps. A proof is not considered done until the user confirms it in jEdit.
- Be extra careful with proof methods like metis, blast, auto as the may not terminate.
- Avoid triggering full-file reprocessing whenever possible. Prefer narrow line-range/offset MCP checks and small local edits, with short timeouts.

## Tools

- The AI only uses Sledgehammer for smaller subgoals, and never for the entire lemma.
- **Sledgehammer**: the assistant can run it via MCP when stuck or to close subgoals.
- **find_theorems**: the assistant searches for relevant lemmas proactively when needed.

## Dead Ends

- When an approach seems unproductive, the assistant flags it immediately and suggests alternatives.
