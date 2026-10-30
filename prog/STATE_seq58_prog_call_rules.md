# STATE_seq58_prog_call_rules
Updated: 2026-10-30

## Cursor
- component: C4
- status: in_progress
- active_file: prog/vfmProgScript.sml
- next_action: Inspect .holbuild/logs/current/verifereum/vfmProgTheory/build.log's eight Type.mk_vartype %%gen_tyvar%% warnings: determine whether checkpoint-generated noise or source parser warnings, and resolve or escalate as needed. All proofs now pass. Finish final audit/doc status and commit the uncommitted integrity-audit code and task-owned memory. Do not restart resolved witness investigation.
- expected_goal_shape: No failing theorem: whole vfmProgTheory builds. Remaining audit issue is eight non-standard generated type-variable warnings in build.log; final clean status/commit and statement audit documentation pending.
- verify_with: holbuild(targets=['vfmProgTheory'], timeout=1800); grep warning/cheat/error in public build.log; git diff --name-only 48d42165; git status --short

## If This Fails
- Stay in C4; checkpoint useful partial audit evidence. If warnings require new proof/tooling decomposition, escalate to strategist. Close C4 only after final criteria are validated, then review and end complete.

## Do Not Retry
- Reopen charged inner-revert witness or report main CALL theorem unprovable: Owner explicitly authorized uncharged child constructions; both repaired witnesses checked and all rules now build.
  - evidence: episode:E0034
  - evidence: episode:E0035
  - evidence: episode:E0037

## Reflection
### Tunnel Vision Check
- Fresh expert should question whether Type.mk_vartype generated-name warnings are holbuild checkpoint serialization rather than source parser problems; do not suppress warnings blindly.
- The proof decomposition has succeeded: all main and tail rules build. Do not optimize already-proved CALL helpers or reopen historical false witness.
- Outside-the-box oracle audit used Tag.dest_tag on exported DB.thms because generated Theory.txt is absent; audit is enforced during build, not a trusted assertion.

### What Went Wrong
- The old human-decision block was resolved by explicit owner M0001 authorization. Both local witness child records now pin newAccountCharged := F, and credit_new_account_def was needed in execution normalization.
- SPEC_Return_inner failed only because Abbrev stateCost=0 hid its scalar bound. Eliminating alias fixed all branches.
- Both SELFDESTRUCT Code-output branches needed word_size 0 normalized; adding word_size_def fixed entire theory.
- Final audit unexpectedly found eight generated type-variable warnings despite terse successful holbuild output; task's no-parser-warning condition remains to assess.

### Ignored Signals
- Do not compare against c1368161 for file-scope audit: pre-task 48d42165 changed spec/prop/vfmHandleStepScript.sml. Correct audited starting baseline is 48d42165, and all subsequent changed paths are prog/.

### Strategy Adjustments
- Finish audit only. Current uncommitted source change is seven-line build-time oracle integrity check at EOF, already built successfully.
- STATE/LEARNINGS were untracked; task file is tracked. This handoff replaces stale blocked STATE. Include useful task-owned memory in final scoped commit to obtain clean status.
- No task status update or final audit-note update made yet. Task still says planned.

### Oracle Feedback
- Accepted E0034/E0035 witness repairs; C2 suspected-falsehood gate released after separate replan.
- Accepted E0036: zero alias elimination sufficient for SPEC_Return_inner.
- Accepted E0037: word_size normalization sufficient for all tail rules. C4 is sole remaining executable component.

## Evidence Pointers
- episode:E0038 - nonterminal final-audit progress
- tool_output:TO_seq58_prog_call_rules-20261030T162928Z_m0797_t001 - complete theory builds with enforced oracle check
- tool_output:TO_seq58_prog_call_rules-20261030T162928Z_m0804_t001 - eight Type.mk_vartype warnings
- tool_output:TO_seq58_prog_call_rules-20261030T162928Z_m0802_t001 - only prog paths changed relative correct baseline
- tool_output:TO_seq58_prog_call_rules-20261030T162928Z_m0781_t001 - witness statement exceptions and later proof-only changes
- tool_output:TO_seq58_prog_call_rules-20261030T162928Z_m0779_t001 - broad original-source diff (large output truncated near tail)
- tool_output:TO_seq58_prog_call_rules-20261030T162928Z_m0780_t001 - prohibited-construct grep, no cheat, pre-existing TRY/ORELSE sites
- source:prog/CALL_RULES_AUDIT_seq58.md - baseline 48d421654525f06680177d4f5d64374cd56f6320 inventory
