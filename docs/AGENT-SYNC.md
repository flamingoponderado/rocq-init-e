# Two-agent synchronization

The coordinator works in `rocq-init-e` on local `main`. The GPT-6.1-sol low
worker works in `rocq-init-e-verifier`, initially on `agent/verifier-review`
and subsequently on separately named task branches such as
`agent/store-simulation`. These are separate Git checkouts and build outputs.

Coordination uses the agmsg provided Bash scripts, team `rocq-init-e`,
identities `rocq-main` and `rocq-verifier`. Do not access its database or team
configuration directly.

1. Coordinator assigns an exclusive file/task scope and base commit.
2. Worker acknowledges base SHA and scope before editing.
3. Dependency changes, shared-file edits and heavy jobs require coordination.
4. Worker commits clean tested changes and pushes only its own remote branch.
   Force pushes and pushes to `main` are prohibited for the worker.
5. Worker sends READY with commit SHA, actual tests and remaining obligations.
6. Coordinator reviews, cherry-picks, builds in the coherent main dependency
   tree, and sends INTEGRATED with the resulting SHA.
7. Worker starts the next task from an announced checkpoint only with a clean
   worktree. Existing published task branches remain available for review.

Herdr worker pane is `wH:p5`; coordinator pane is `wM:p1`. Revalidate live
pane identity before sending prompts; identifiers are specific to this
session. Arm `herdr agent wait` only after observing the worker working.
A settled lifecycle event is a notification to inspect results, not proof of
success. Completion messages must not replace build/kernel evidence.

Scratch builds may use main compiled dependencies read-only, but imported
proofs must be rebuilt coherently with Dune after integration. Do not copy
scratch compiled artifacts into the operator build. No agent may restart a
live guest compilation or verifier. Seal regeneration is an operator step
after the final coherent build; a full verifier pass is required before the
completed port is pushed to main.
