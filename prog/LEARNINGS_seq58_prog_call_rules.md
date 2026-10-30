# LEARNINGS_seq58_prog_call_rules

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1.2' tags=bind,RHS-only,record_update,irule,drule
shape: Successful operation equation with context parameters only in a premise/RHS; simp does not rewrite, or irule fails on simplified record projections
pattern: Derive an instantiated application equality, then simplify the bind with that equality. Name an intermediate head context (FST (HD st.contexts)) before updating it. For getters whose return projection simplifies away the record, establish st.contexts=(head,k)::cs and drule the getter equation instead of irule on its simplified output.
works_when: Straight-line successful CALL prefix operations on a known nonempty explicit head context.
evidence:
- episode:E0004
- source:prog/vfmProgCallPrefixProbeScript.sml:182-224
- tool_output:TO_seq58_prog_call_rules-20261030T113558Z_m0083_t001

## L0002 scope='C1.2.3' tags=tuple,paired_lambda,pure_ss,bind_assoc,BETA_TAC
shape: Structurally equivalent monadic programs differ by paired bind continuations versus FST/SND projections
pattern: Normalize paired application and unapplied paired function forms with generic local equalities. Restrict normalization to pure_ss with LET_THM, ignore_bind_def, bind_assoc and return_bind; follow with BETA_TAC, projection rewrites and explicit REFL_TAC. pure_ss may leave an alpha-identical equality unsolved.
works_when: Structural regrouping only, semantic operations opaque; see step_call_segments.
evidence:
- tool_output:TO_seq58_prog_call_rules-20261030T113558Z_m0136_t001
- source:prog/vfmProgCallPrefixProbeScript.sml:261-329

## L0003 scope='C1.2.3' tags=bind,polymorphism,opaque,std_ss
shape: Compose known producer success equation into an arbitrary-continuation bind
pattern: Use backward irule call_bind_success from a typed bind goal (or derive a typed opaque continuation equation), not forward drule from the producer alone. Restricted std_ss bind reduction requires explicit pairTheory.pair_case_thm and sumTheory.sum_case_def. Final record equality can use srw_ss without assumptions to preserve scalar names.
works_when: unspecified
evidence:
- source:prog/vfmProgCallPrefixProbeScript.sml:483-575
- episode:E0009

## L0004 scope='C1.3.2.1' tags=forfeit_remaining_gas,invariant,consume_gas
shape: Raw-state exact failure-handler equality assigns gasUsed=gasLimit
pattern: forfeit_remaining_gas composes get_gas_left and guarded consume_gas, so after restoration it requires used-sp<=gasLimit. SPEC wf_state may supply this, but raw arbitrary-state helpers must carry an explicit child bound. A parent bound is not needed once forfeiture succeeds.
works_when: unspecified
evidence:
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0278_t001
- source:spec/vfmExecutionScript.sml:646-650

## L0005 scope='C2.1.1' tags=simp,call_gas,native-transfer
shape: Transferred meter proof leaves dynamicGas + (if 0 < value then call_stipend else 0) = stipend
pattern: Main imports call_gas_zero_cost[simp], absent from prefix probe; at final meter leaf push the call_gas pair equality with qpat_x_assum and simp[call_gas_def]. Avoid reopening monadic spine.
works_when: unspecified
evidence:
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0380_t001
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0385_t001

## L0006 scope='C1.3.2.3' tags=polymorphism,reraise,handle_create
shape: Forwarded handle_create NONE equation fails to rewrite unit handle_step
pattern: Annotate auxiliary create equality at unit execution_result when composing with handle_step; otherwise drule can instantiate its polymorphic reraise result independently from the goal.
works_when: unspecified
evidence:
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0343_t001
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0350_t001

## L0007 scope='C2.1' tags=call_gas,AC,simp,performance
shape: call_gas pair equation differs only by association/commutation of gas-cost sum
pattern: Move only the matching call_gas equality assumption to goal with qpat_x_assum ... mp_tac, then simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]. Avoid global gvs AC over all state and continuation assumptions; pure_ss normalizes but may leave P=>P.
works_when: unspecified
evidence:
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0442_t001
- tool_output:TO_seq58_prog_call_rules-20261030T133624Z_m0438_t001

## L0008 scope='C2.1' tags=prefix,result-adapter,drule_all
shape: Native semantic equation conclusion has nested records that fail irule matching
pattern: Use local result-variable transitivity adapter: native hypotheses plus native RHS=result imply program=result. Prove by strip_tac, drule_all native equation, specialize continuation only, gvs. Consumer can then explicitly witness antecedent variables and normalize the output equality.
works_when: unspecified
evidence:
- episode:E0020
- source:prog/vfmProgScript.sml:5292-5327

## L0009 scope='C2.2' tags=arithmetic,aliases,prefix,base-cost
shape: Prepared CALL adapter requires base execution-cost bound while source has total bound and gasCost equality
pattern: Derive base bound before expanding aliases using local elementary call_base_cost_bound and witness dynamicGas. Then gvs[EL_TAKE,GSYM ADD_ASSOC] normalizes premises together; split call_has_value to discharge remaining TAKE selectors. Avoid arithmetic over expanded conditional stack/cost terms.
works_when: unspecified
evidence:
- episode:E0026
- source:prog/vfmProgScript.sml:5835-5910

## L0010 scope='C2.2' tags=gvs,simp,conditional,normalization
shape: Continuation balance guard remains despite sufficient balance assumption
pattern: Normalize assumptions and goal together with gvs, not simp alone, when rewriting comparison syntax (e.g. GSYM NOT_LESS_EQUAL changes 0< to neq within conditionals). Otherwise the sufficient balance assumption may no longer syntactically match the rewritten guard.
works_when: unspecified
evidence:
- tool_output:TO_seq58_prog_call_rules-20261030T153638Z_m0569_t001
- tool_output:TO_seq58_prog_call_rules-20261030T153638Z_m0571_t001

## L0011 scope='C2.4' tags=Abbrev,stateCost,restored_unused_gas
shape: Revert scalar bound retains Abbrev(stateCost=0) while restoration identity expects g+memory_cost
pattern: Eliminate Abbr stateCost at Revert branch entry, along with returnCode/gasCost aliases, before applying restored_unused_gas. Avoid alias replacing every literal zero in semantic expressions.
works_when: unspecified
evidence:
- episode:E0036
- source:prog/vfmProgScript.sml:6904

## L0012 scope='C3' tags=SELFDESTRUCT,word_size,deposit,Code
shape: SELFDESTRUCT empty-code deposit leaves keccak256_per_word_cost * word_size 0
pattern: Include word_size_def in the bounded final handler simplification for both outermost and inner branches; otherwise a zero hash-cost obligation can reach a later set/extensionality dispatcher and masquerade as a structural failure.
works_when: unspecified
evidence:
- episode:E0037
- source:prog/vfmProgScript.sml:7208
- source:prog/vfmProgScript.sml:7332
