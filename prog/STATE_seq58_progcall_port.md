# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.6.5.2
- status: in_progress
- active_file: prog/vfmCallGrantScript.sml
- next_action: Build vfmCallGrantTheory to check the last edit restoring literal n <= LENGTH u.contexts before drule_all in call_meter_reserved_proceed_call. The analogous proceed_create wrapper may need the same repair. Then implement abort_unuse/abort_call_value reservation discharge and abort_create/abort_create_exists ordinary-result adapters. GrantScript is new uncommitted partial work. EntryStep and Reserve are checked and committed (d473563a, dd601956); E0024 was reviewed and accepted.
- expected_goal_shape: Last failure: all proceed_call budget premises held, but gvs had rewritten the length premise to n <= SUC (LENGTH rest), so drule_all did not match. Last edit reasserts n <= LENGTH u.contexts by simp, not yet built. CALL payment was checked before that failure. CREATE wrapper has not yet been reached. Abort composition must preserve ordinary results on early errors, not claim unconditional refund.
- verify_with: holbuild(targets=["vfmCallGrantTheory"], timeout=1800)

## If This Fails
- Inspect the actual wrapper premise mismatch; use directed matching and restore literal boundary premises. Keep checked scalar/reservation interfaces opaque. Record useful partial evidence via checkpoint_progress; close stuck and request review only for structural interface failure or false margin. No further export weakening.

## Do Not Retry
- Infer reservation or paid stipend surplus from call_meter_result.: That interface has forgotten the surplus; use call_meter_reserved and its transport laws.
  - evidence: episode:E0023
  - evidence: episode:E0024
- Unrestricted nonempty-context CALL safety or constrain external caller beyond the authorized amendment.: Historical checked counterexamples require rooted fresh-callee budget. No further exported guards are authorized.
  - evidence: episode:E0011
  - evidence: episode:E0013
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0272_t001
- Unfold whole step_call, proceed_call, dispatch and crypto together.: Checked entry/reservation/dispatch boundaries now provide the intended compositional interface.
  - evidence: episode:E0021
  - evidence: episode:E0023
  - evidence: episode:E0024

## Reflection
### Tunnel Vision Check
- Outside-the-box isolation in EntryStep/Reserve/Grant theories remains effective. The unconsidered alternative is a more generic state-preserving reader/neutral interface, but current reservation transport already avoids opcode unfolding; do not redesign it merely for routine matching.
- The original result contract was the wrong abstraction for paid stipends: it discards surplus. The strategist's reserved predicate now retains exactly the needed backing and claim credit. This decomposition is still appropriate.
- A fresh expert should first scrutinize abort ordering and error states: abort_unuse refunds before push, whereas some other abort paths can fail before refund. Never infer unconditional refund from an ordinary-result contract.
- Reader specialization consumed too many tactical retries. Inspect polymorphism and beta normalization earlier rather than varying match tactics.

### What Went Wrong
- call_meter_result could not transport the paid stipend surplus; this was escalated before whole-opcode unfolding. Oracle introduced call_meter_reserved and transport laws, now checked.
- Broad metis on arithmetic-reordered margin inequalities timed out. Explicitly establish the theorem-shaped sum inequality by decide_tac, then drule_all and normalize AC sums.
- Polymorphic context reader Q.SPEC_THEN could not instantiate its result type; Q.ISPEC_THEN with MATCH_ACCEPT_TAC o BETA_RULE resolved it. Lowercase match_accept_tac does not exist.
- The last Grant wrapper failure is a syntactic boundary mismatch: simplification removed n <= LENGTH u.contexts. Reintroduce literal boundary facts before directed application rather than unfolding budget internals.

### Ignored Signals
- Safe adapters whose post is call_meter_ready cannot be rewritten as result-post adapters without consequence/transport; retain exact postconditions.
- Automatic existential witness names changed after strip_tac. goal_assum (drule_at Any) was more robust than guessing d'.
- Free theorem variables under mp_tac do not automatically specialize to the current d/cost. GEN_ALL plus beta normalization enabled drule_all in the consume adapter.

### Strategy Adjustments
- Keep reservation acquisition and discharge separate from whole opcode assembly. Error paths may forget the reservation, but successful grant payment/entry must retain and spend it.
- EntryStep proves arbitrary-address proceed_call by guarded dispatch, with all crypto opaque. ReserveTheory proves all requested C1.3.6.5.1 transport/adapters/readers and is committed.
- GrantTheory has checked consume acquisition, withholding and restore-child discharge; CALL payment was also checked in the latest failing build. Remaining work is wrapper normalization and abort adapters.

### Oracle Feedback
- TO_m0710 introduced a fixed-anchor reservation rather than more per-opcode arithmetic plumbing; its zero, weakening, neutral and charge/credit probes all succeeded.
- E0024 accepted the reservation interface without changing frozen exports. This is infrastructure completion only, not final CALL-rule completion.

## Evidence Pointers
- episode:E0023 - checked scalar margins and general proceed_call; missing surplus interface identified
- episode:E0024 - reservation interface proved
- tool_output:TO_seq58_progcall_port-20261031T134530Z_m0763_t001 - E0024 accepted
- tool_output:TO_seq58_progcall_port-20261031T134530Z_m0765_t001 - Reserve checkpoint commit dd601956
- episode:E0025 - partial Grant evidence and exact resume point
- tool_output:TO_seq58_progcall_port-20261031T134530Z_m0775_t001 - first four Grant theorems build clean
- tool_output:TO_seq58_progcall_port-20261031T134530Z_m0777_t001 - latest failure, after CALL payment checked
- tool_output:TO_seq58_progcall_port-20261031T134530Z_m0778_t001 - last unbuilt literal-length edit
- source:prog/vfmCallReserveScript.sml
- source:prog/vfmCallGrantScript.sml
