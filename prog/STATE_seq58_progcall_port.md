# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.10
- status: ready
- active_file: prog/vfmCallReturnScript.sml
- next_action: Resume begun C1.3.10. Verify vfmCallReturnTheory, then inspect old call_memory_final_pop/run_call_memory_returns in vfmProgCallScript.sml (1559-1618 and later) and checked handle_exception_memory_return plus meter restore/settlement boundaries. Build final-pop and finite memory-return interfaces over the isolated vfmCallReturnTheory; replace gasUsed-only post records by exact semantic context transforms and bound actual post-restoration refund via root claim. No source edits have been made for C1.3.10 yet.
- expected_goal_shape: At final root depth, budget bounds child claim by ceiling. Actual refundable execution gas after restore/forfeit is <= claim, hence <= grant <= caller.gasUsed. Returned caller context must express absorb_state_gas, failure credit_new_account or success repay_state_gas_spill_context plus memory/pc/stack/rollback observations.
- verify_with: holbuild(targets=["vfmCallReturnTheory"], timeout=1800)

## If This Fails
- Use checked semantic boundary lemmas rather than unfolding merged records. Record partial evidence with checkpoint_progress; escalate structural interface gaps to strategist. Do not add caller backing or export guards.

## Do Not Retry
- Expand settled merged semantic records with backed/claim/absorb/repay definitions in consumers: Repeated record normalization timed out in earlier work; use call_meter_pop_settle_pair and scalar settlement corollaries.
  - evidence: episode:E0041
  - evidence: episode:E0042
- Infer unconditional root nonforbidden exceptions from call_meter_budget alone: Budget exit intentionally permits unuse_gas failure after the pop. Ordinary-return proof instead combines scoped inner safety with full-wf-derived gas_stack_ok/stack_room_ok handler interfaces.
  - evidence: episode:E0046
  - evidence: episode:E0049

## Reflection
### Tunnel Vision Check
- Outside-the-box simplification succeeded: weakening handler input from full wf_state to EVERY (wf_context o FST) avoided reconstructing a large intermediate invariant; the exact smaller invariant follows directly from decreases_gas_cred_step_inner.
- Fresh expert should question whether final-pop proof is bounding pre-restore gas instead of actual restored refund. Preserve committed/spill distinctions and use compact scalar interfaces.
- Do not optimize the old unrestricted safety chain: new isolated vfmCallReturnTheory already proves scoped finite ordinary return. Integration must remove/replace obsolete local helpers later.
- The decomposition remains appropriate after revised C1.3.8.2: budget preservation and ordinary return are separate interfaces. C1.3.10 should operate on final semantic context transforms, not gasUsed-only records.

### What Went Wrong
- Generic metis_tac[call_meter_safe_def] timed out; selecting the live safe assumption, unfolding only its definition and specializing at the actual result solved immediately.
- Cases_on unannotated handle_create e s selected a polymorphic result instance that could not rewrite the unit-typed handler case. Explicit unit execution_result annotation fixed it.
- same_frame_or_grow_length concludes GREATER_EQ, not syntactic <=; metis needed GREATER_EQ.
- gvs removed arithmetic facts implied by stronger bounds; drule_all then required restating 0<n or 2<=LENGTH contexts explicitly.

### Ignored Signals
- Full wf_state contains gas_stack_ok and stack_room_ok, and existing handler safety already consumes their intermediate preservation. Initial concern that root nonabort necessarily required an additional caller condition was too pessimistic for the full-wf run invariant.
- Semantic consumer equality proofs must avoid simplifying by the current result equation prematurely; NoAsms in the handler decomposition equality prevents losing the compositional shape.

### Strategy Adjustments
- C1.3.8.2 and C1.3.9 completed, reviewed, committed. Latest commits: 5b53ea87 (step budget) and 9b64dd9e (finite ordinary return); earlier handler checkpoints f49a74e8 and 047767bf.
- New prog/vfmCallReturnScript.sml isolates valid finite-return machinery from the still-obsolete unrestricted local safety chain in vfmProgCallScript.sml. Upcoming final-pop/summary integration owns replacement of those old consumers.
- C1.3.10 has been begun, but only existing final-pop source was read. No partial proof experiment or uncommitted source remains; git status clean at handoff.

### Oracle Feedback
- Strategist's smaller context-wf boundary insight held: all three handler budget lemmas strengthened in place and step_inner_contexts_wf made step composition short.
- E0048 review certified budget preservation only, not unconditional nonabort. E0049 then certified scoped ordinary return using full-wf run invariant and existing handler safety, without extra exported assumptions.
- Acceptance of isolated vfmCallReturnTheory does not imply vfmProgCallTheory builds; obsolete unrestricted local chain and export consumers remain integration work.

## Evidence Pointers
- episode:E0048 - revised step budget leaf proved and reviewed
- episode:E0049 - scoped finite ordinary return proved and reviewed
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1450_t001 - clean vfmCallInnerTheory build
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1472_t001 - clean vfmCallReturnTheory build
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1474_t001 - strategist accepted finite-return boundary and identified integration responsibility
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1479_t001 - old final-pop source/interface to port
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1482_t001 - clean git status
- source:prog/vfmCallInnerScript.sml:1394-1502 - context-wf handler and step budget boundaries
- source:prog/vfmCallReturnScript.sml - isolated scoped finite-return theory
