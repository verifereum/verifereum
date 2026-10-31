# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.6.2
- status: in_progress
- active_file: prog/vfmProgCallScript.sml
- next_action: Inspect shared post tactic (~1434) by inlining its initial stages in Resume SPEC_Call_any[post] (~1535), stopping immediately before qexistsl_tac. Latest build verifies new wrapper-based entry and reaches post, which fails 'goal not an exists'. Determine which existential(s) early simp or conversion removed before selecting witnesses. Public formulas are already ported; do not restate again. C1.6.1 reviewed/committed b6c3dcf5; subsequent shared entry refactor is uncommitted.
- expected_goal_shape: Resume SPEC_Call_any[post]: separation post plus CODE_POOL; legacy shared post tactic fails goal not an exists during new 14-witness selection. Inner failing witness/stage not isolated. Entry application now checked; stipend/frame applications not yet validated.
- verify_with: holbuild(targets=["vfmProgCallTheory"], timeout=1800)

## If This Fails
- Read instrumented Resume stage goals rather than macro top goal. Use supplied ready-result projections; remove legacy semantic unfolding in shared post. Checkpoint useful progress; escalate actual interface obstruction or 3 honest failed approaches, without changing public formulas or adding guards.

## Do Not Retry
- Use old g+gasCost-gasLeft gas post or count settlement refund in gasLeft: gasLeft is child unused execution gas, not spill repayment/creation credit. Canonical semantic merged carrier is approved replacement.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T211644Z_m1757_t001
- Rebuild aliases after simplifying unprotected call_entry_prepared or backward-irule meter projection conjunction: Simplification eliminates witnesses; backward matching lacks premise-only parameters. Protected wrapper and forward elimination are checked replacements.
  - evidence: episode:E0059
  - evidence: episode:E0060
- fs over full ready wrapper context or GSYM Abbrev_def in simp: Expands large record expressions or loops; use independent per-assumption normalization and targeted substitution.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T211644Z_m1806_t001
  - evidence: tool_output:TO_seq58_progcall_port-20261031T211644Z_m1817_t001

## Reflection
### Tunnel Vision Check
- Fresh expert should question whether early simp in the old post tactic eliminates merged or other existential witnesses; the witness list is not yet validated against the live converted goal.
- Do not optimize execution semantics: entry, observation and meter boundaries now check. Remaining work is separation packaging and framing.
- Unconsidered alternative: convert SEP_EXISTS before simplification or pick witnesses one at a time with literal EXISTS_TAC to preserve their names. Inspect first rather than guess.
- The opaque ready-result boundary is the correct abstraction; no new invariant appears needed. If missing projections arise, extend that boundary instead of unfolding settlement in public consumers.

### What Went Wrong
- Whole-theorem SIMP_RULE on call_entry_prepared eliminated success/out/gasLeft witnesses; old shared tactics had never been validated against this new result. Initial alias reconstruction grew brittle and was replaced by strategist-designed opaque predicate.
- Backward irule on projection conjunction could not determine premise-only mr/caller parameters; forward application while named final equality is available succeeded.
- fs across the symbolic record context expanded unrelated aliases and timed out. Clear input premises after entry application and normalize each result theorem independently.
- REWRITE_RULE [definition,LET_THM] left lambda application; predicate elimination needed SIMP_RULE to beta-normalize before strip_assume_tac.

### Ignored Signals
- Macro failure output shows its top input, not inner failing state. Inline/suspend stages for useful local goals.
- Opaque result predicates protect existential names during wrapper simplification; do not unfold until after eliminating the existential witnesses.
- GSYM Abbrev_def is not a safe generic simplification rule. Use targeted abbreviation substitution or forward definition rewriting.

### Strategy Adjustments
- Both exports now use canonical merged semantic meter carriers per strategist, retain child gasLeft bound, and own all four meter resources.
- Checked call_entry_ready_prepared packages all execution, rollback, stipend, observation and meter facts. call_entry_ready_def is its accepted one-time elimination equation.
- C1.6.2 now consumes this wrapper and deletes the 40-line alias reconstruction experiment. Entry reaches Resume post successfully; do not claim full exports proved.

### Oracle Feedback
- First clarification supplied exact public canonical carrier formula and distinguished entered from success; implemented without further guards.
- Second augmentation replaced brittle shared-tactic reconstruction with protected result predicate; that insight held and C1.6.1 was accepted (E0060).
- Review accepted definition equation itself as elimination interface; no duplicate conjunction theorem required. Bounded checkpoint was authorized despite known downstream incomplete exports.

## Evidence Pointers
- episode:E0060 - checked/reviewed protected entry boundary
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1819_t001 - bounded boundary closure accepted
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1822_t001 - b6c3dcf5 checkpoint commit
- episode:E0061 - current shared entry progress and post failure
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1828_t001 - latest build reaches post, witness error
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1757_t001 - exact approved canonical public meter formula
