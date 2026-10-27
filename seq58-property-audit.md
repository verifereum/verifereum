# EIP-8037 property realignment: certification and contract audit

Audit date: 2026-10-27. Source checkpoint: `896b76f3`; comparison baseline: `78466c68`.

## Result and owner clarification request

Technical proof repair is green for all 20 changed, task-owned theories listed below. The root build reaches an **out-of-scope** failure in `prog/vfmProgScript.sml`, `SPEC_Stop_inner`, line 1750, `metis_tac[option_CASES]`; the remaining goal contains opaque `repay_state_gas_spill`. No repair to that file was attempted by this audit.

**This is not a frozen-contract completion certificate.** The final audit found inherited statement changes outside the TASK's explicit exception list. The strategist's audit ruling requires owner clarification, not restoration or additional proof work. Please explicitly approve or reject these additional exceptions:

1. Commit `133bc150`: six statements in `spec/prop/vfmAccountFrameScript.sml` add the reservoir argument to `initial_context`, with a corresponding existential `sg`:
   - `proceed_call_nonprecompile_frame`: `exists static t` becomes `exists static sg t`; `initial_context code static rd t` becomes `initial_context code static rd sg t`.
   - `proceed_call_nonprecompile_message`: `exists tx` becomes `exists sg tx`; the initial context's final `rd tx` becomes `rd sg tx`.
   - `step_call_push_new_frame`: `exists code static mr t` becomes `exists code static sg mr t`; `(Memory mr) t` becomes `(Memory mr) sg t`.
   - `proceed_create_frame_effects`: `exists t` becomes `exists sg t`; `(initial_context address code F (Code address) t)` becomes `(initial_context address code F (Code address) sg t)`.
   - `step_create_push_new_frame`: `exists code t` becomes `exists code sg t`; the initial context gains `sg` immediately before `t`.
   - `step_push_new_frame`: `exists code static rd t` becomes `exists code static rd sg t`; the initial context gains `sg` immediately before `t`.
   All other hypotheses and conclusion conjuncts of these statements are unchanged. These are arity migrations, but the supplied TASK freezes text as well as intent.
2. Same commit, `spec/prop/vfmRunCallScript.sml`, `run_call_preserves_storage_outside_accessed_slots_initial`: hypothesis `es.contexts = [(initial_context callee code static rd t, es.rollback)]` becomes `es.contexts = [(initial_context callee code static rd sg t, es.rollback)]`. `sg` is universally quantified, not existential.
3. Commit `86b5d5f9`, `spec/prop/vfmRunCallScript.sml`, `step_pop_structure`: removed the conclusion conjunct
   ```sml
   new_head.gasUsed >= (FST parent).gasUsed -
     ((FST (HD s.contexts)).msgParams.gasLimit -
      (FST (HD s.contexts)).gasUsed)
   ```
   The rest of the statement (same hypotheses, pop shape, parent's msgParams, and two storage alternatives) remains. This is a substantive weakening, not an arity repair.
4. Same commit, `spec/prop/vfmRunWithinFrameScript.sml`, deleted the following complete baseline statements:
   ```sml
   Theorem step_same_frame_gas_monotone:
     outputTo_consistent s /\ s.contexts <> [] /\
     EVERY (wf_context o FST) s.contexts /\ step s = (r,s') /\
     LENGTH s'.contexts = LENGTH s.contexts ==>
     (FST (HD s.contexts)).gasUsed <= (FST (HD s'.contexts)).gasUsed

   Theorem run_within_frame_gas_monotone:
     outputTo_consistent es /\ wf_state es /\
     run_within_frame es = SOME (r,es') /\
     LENGTH es'.contexts = LENGTH es.contexts ==>
     (FST (HD es.contexts)).gasUsed <= (FST (HD es'.contexts)).gasUsed
   ```
   Current form: absent. The expressly approved replacements of the distinct `step_inst` and `step_inner` theorems do not themselves authorize these deletions.

Commit messages explain the historical decisions, but provenance alone is not authority to enlarge the supplied TASK exception list. No new counterexample to these exact disputed obligations was checked in this audit; do not confuse this report with a new unprovability certificate. No statement was changed during this audit.

## Current-session build evidence

Fresh-session confirmation: all 20 targets below were requested together again and returned `holbuild finished in 0.135s` (cached success), evidence `TO_seq58_prop_repos-20261027T144253Z_m1668_t001`. No source changed between these certifications. The preceding root reproduction is `TO_seq58_prop_repos-20261027T144253Z_m1662_t001`.

Tool interface: `holbuild(targets=[...], timeout=1800)`; this is the supported replacement for legacy CLI commands, not a claim to have run a shell. One successful invocation requested **all** targets in the table below. It finished with `holbuild finished in 73.951s`. Cached targets were accepted without rebuilding; `vfmSettlementTheory` and `vfmOriginalAccountsTheory` printed explicit `built` lines. Excluded `vfmComputeTheory` rebuilt successfully as a dependency, without edits by this audit. A separate `vfmRunCallTheory` invocation finished in 0.104s. The per-target equivalent requested by the TASK is `holbuild -j4 build <target>` for every row; all rows returned successfully in that current-session multi-target invocation.

| Source (all paths relative to project root) | Target | Result |
|---|---|---|
| spec/prop/vfmAccountDeletionScript.sml | vfmAccountDeletionTheory | success |
| spec/prop/vfmAccountFrameScript.sml | vfmAccountFrameTheory | success |
| spec/prop/vfmCallDrainProbeScript.sml | vfmCallDrainProbeTheory | success |
| spec/prop/vfmDomainCollectionScript.sml | vfmDomainCollectionTheory | success |
| spec/prop/vfmDomainSeparationScript.sml | vfmDomainSeparationTheory | success |
| spec/prop/vfmGasStackProbeScript.sml | vfmGasStackProbeTheory | success |
| spec/prop/vfmHandleStepScript.sml | vfmHandleStepTheory | success |
| spec/prop/vfmHeadStackScript.sml | vfmHeadStackTheory | success |
| spec/prop/vfmJumpDestScript.sml | vfmJumpDestTheory | success |
| spec/prop/vfmMsdomainPreservedScript.sml | vfmMsdomainPreservedTheory | success |
| spec/prop/vfmPopGasProbeScript.sml | vfmPopGasProbeTheory | success |
| spec/prop/vfmRunCallScript.sml | vfmRunCallTheory | success |
| spec/prop/vfmRunWithinFrameScript.sml | vfmRunWithinFrameTheory | success |
| spec/prop/vfmSameFrameScript.sml | vfmSameFrameTheory | success |
| spec/prop/vfmSstoreGasProbeScript.sml | vfmSstoreGasProbeTheory | success |
| spec/prop/vfmStaticCallsScript.sml | vfmStaticCallsTheory | success |
| spec/prop/vfmStepLengthScript.sml | vfmStepLengthTheory | success |
| spec/prop/vfmStoragePredicatesScript.sml | vfmStoragePredicatesTheory | success |
| tests/vfmOriginalAccountsScript.sml | vfmOriginalAccountsTheory | success |
| tests/vfmSettlementScript.sml | vfmSettlementTheory | success |

Root equivalent `holbuild -j4 build`, via `holbuild(timeout=1800)`, stops at the external `vfmProgTheory` failure described above. It does not fail in owned `spec/prop` or `tests`.

Evidence IDs: `TO_seq58_prop_repos-20261027T144253Z_m1632_t001` (20 targets), `..._m1628_t001` (RunCall), `..._m1640_t001` (root). Tool output `..._m1631_t001` is the complete owned baseline source diff; `..._m1642_t001` and `..._m1643_t001` give the disputed commits' full explanations.

## Files and integrity checks

The table above is the complete changed task-owned SML inventory against the baseline (18 property/probe files and two tests). `seq58-property-audit.md` and `seq58-added-lemmas.md` are report artifacts added by this audit. No SML source edits were made in this audit session.

The baseline-to-HEAD aggregate diff additionally contains changes from other runs to `prog/vfmProgScript.sml`, `spec/prop/vfmComputeScript.sml`, `spec/prop/vfmDecreasesGasScript.sml`, and `spec/prop/vfmOriginalStateScript.sml`. These are not claimed as this task's proof edits; they were not modified by this audit. The distinction matters because the repository contains merged concurrent work.

Searches for `cheat`, `new_axiom`, `mk_oracle_thm`, and raw `hh` in all property and test scripts returned no matches. The source diff shows no tactic-timeout change and no added TRY/ORELSE wrapper around a search tactic; existing/added composition alternatives use structural `irule`/simplification, not search fallback. The initial git status was clean.

**Oracle-tag audit limitation:** no generated `*Theory.txt` is exposed by this tool installation: `.holbuild/gen` does not exist, `.holbuild/obj` contains no matching indexes, and recursive project discovery finds none. Thus the required independent Theory.txt oracle-tag inspection could not be certified. This report does not claim that the missing index was inspected. The successful builds and cheat-free source are retained evidence, but are not a fabricated index audit.

All added theorem names and complete statements (including local boundaries and diagnostic witnesses) are catalogued in `seq58-added-lemmas.md`. The pre-existing `cp_state_gas_meter[simp]` was proved rather than added; its statement is also included there for family coverage. Relocated pre-existing `preserves_domain_has_callee_fail`, `preserves_domain_has_callee_unuse_gas`, and `preserves_rollback_unuse_gas` are not misreported as new lemmas.
