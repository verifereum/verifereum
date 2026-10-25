Theory vfmProg
Ancestors
  vfmExecution vfmExecutionProp vfmContext vfmConstants vfmDecreasesGas vfmState vfmRunCall
  vfmTypes vfmBuffer
  prog words set_sep pred_set pair list arithmetic option finite_map combin
Libs
  wordsLib intLib

(*-------------------------------------------------------------------------------*
   State set
 *-------------------------------------------------------------------------------*)

Datatype:
  evm_el = Stack      (bytes32 list)                     (* from top context *)
         | Memory     buffer   (* compared as a buffer: see vfmBuffer *)
         | PC         num
         | JumpDest   (num option)
         | ReturnData (byte list)
         | GasUsed    num
         | AddRefund  num
         | SubRefund  num
         | Logs       (event list)
         | MsgParams  message_parameters
         | Parsed     num (opname option) bool
         | Exception  (unit + exception option)
         | Contexts   ((context # rollback_state) list)  (* other contexts *)
         | CachedRB   rollback_state
         | TxParams   transaction_parameters
         | Rollback   rollback_state
         | Msdomain   domain_mode
End

Type evm_set = “:evm_el set”;

(*-------------------------------------------------------------------------------*
   Converting from execution_state record to v_set
 *-------------------------------------------------------------------------------*)

Datatype:
  evm_dom = HasStack
          | HasMemory
          | HasPC
          | HasJumpDest
          | HasReturnData
          | HasGasUsed
          | HasAddRefund
          | HasSubRefund
          | HasLogs
          | HasMsgParams
          | HasParsed num
          | HasException
          | HasContexts
          | HasCachedRB
          | HasTxParams
          | HasRollback
          | HasMsdomain
End

Definition evm2set_on_def:
  evm2set_on dom (r : unit execution_result) =
    let s = SND r; current_context = FST (HD s.contexts) in
      (if HasStack ∈ dom      then { Stack (current_context.stack) } else {}) ∪
      (if HasMemory ∈ dom     then { Memory (current_context.memory) } else {}) ∪
      (if HasPC ∈ dom         then { PC (current_context.pc) } else {}) ∪
      (if HasJumpDest ∈ dom   then { JumpDest (current_context.jumpDest) } else {}) ∪
      (if HasReturnData ∈ dom then { ReturnData (current_context.returnData) } else {}) ∪
      (if HasGasUsed ∈ dom    then { GasUsed (current_context.gasUsed) } else {}) ∪
      (if HasAddRefund ∈ dom  then { AddRefund (current_context.addRefund) } else {}) ∪
      (if HasSubRefund ∈ dom  then { SubRefund (current_context.subRefund) } else {}) ∪
      (if HasLogs ∈ dom       then { Logs (current_context.logs) } else {}) ∪
      (if HasMsgParams ∈ dom  then { MsgParams current_context.msgParams } else {}) ∪
      (if HasContexts ∈ dom   then { Contexts (TL s.contexts) } else {}) ∪
      (if HasCachedRB ∈ dom   then { CachedRB (SND (HD s.contexts)) } else {}) ∪
      (if HasTxParams ∈ dom   then { TxParams s.txParams } else {}) ∪
      (if HasRollback ∈ dom   then { Rollback s.rollback } else {}) ∪
      (if HasMsdomain ∈ dom   then { Msdomain s.msdomain } else {}) ∪
      (if HasException ∈ dom  then { Exception (FST r) } else {}) ∪
      { Parsed n (FLOOKUP current_context.msgParams.parsed n)
                 (wf_state s)
        | HasParsed n ∈ dom }
End

Definition evm2set_def:
  evm2set s = evm2set_on UNIV s
End

Definition evm2set_without_def:
  evm2set_without x s = evm2set s DIFF evm2set_on x s
End

(* theorems *)

Theorem PUSH_IN_INTO_IF[local]:
  !g x y z. x IN (if g then y else z) <=> if g then x IN y else x IN z
Proof
  metis_tac[]
QED

Theorem evm2set_on_SUBSET_evm2set[local]:
  ∀y s. evm2set_on y s SUBSET evm2set s
Proof
  rw[evm2set_def]
  \\ simp[SUBSET_DEF, IN_UNIV, evm2set_on_def, PUSH_IN_INTO_IF]
  \\ rw[]
QED

Theorem SPLIT_evm2set[local]:
  ∀x s. SPLIT (evm2set s) (evm2set_on x s, evm2set_without x s)
Proof
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,evm2set_without_def]
  \\ `evm2set_on x s SUBSET evm2set s` by METIS_TAC [evm2set_on_SUBSET_evm2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]
QED

Theorem SUBSET_evm2set[local]:
  !u s. u SUBSET evm2set s <=> ?y. u = evm2set_on y s
Proof
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [evm2set_on_SUBSET_evm2set]
  \\ gvs[evm2set_def, SUBSET_DEF]
  \\ qexists_tac `
       (if ∃x. Stack x ∈ u then {HasStack} else {}) ∪
       (if ∃x. Memory x ∈ u then {HasMemory} else {}) ∪
       (if ∃x. PC x ∈ u then {HasPC} else {}) ∪
       (if ∃x. JumpDest x ∈ u then {HasJumpDest} else {}) ∪
       (if ∃x. ReturnData x ∈ u then {HasReturnData} else {}) ∪
       (if ∃x. GasUsed x ∈ u then {HasGasUsed} else {}) ∪
       (if ∃x. AddRefund x ∈ u then {HasAddRefund} else {}) ∪
       (if ∃x. SubRefund x ∈ u then {HasSubRefund} else {}) ∪
       (if ∃x. MsgParams x ∈ u then {HasMsgParams} else {}) ∪
       (if ∃x. Logs x ∈ u then {HasLogs} else {}) ∪
       (if ∃x. Contexts x ∈ u then {HasContexts} else {}) ∪
       (if ∃x. CachedRB x ∈ u then {HasCachedRB} else {}) ∪
       (if ∃x. TxParams x ∈ u then {HasTxParams} else {}) ∪
       (if ∃x. Rollback x ∈ u then {HasRollback} else {}) ∪
       (if ∃x. Msdomain x ∈ u then {HasMsdomain} else {}) ∪
       (if ∃x. Exception x ∈ u then {HasException} else {}) ∪
       {HasParsed n | ∃x y. Parsed n x y ∈ u}`
  \\ rewrite_tac[EXTENSION, EQ_IMP_THM]
  \\ gen_tac \\ strip_tac
  >- (
    strip_tac \\ first_x_assum drule
    \\ simp[evm2set_on_def, PUSH_IN_INTO_IF]
    \\ rw[] \\ goal_assum $ drule )
  \\ simp[evm2set_on_def, PUSH_IN_INTO_IF]
  \\ strip_tac
  \\ first_x_assum drule
  \\ rw[evm2set_on_def] \\ rw[]
QED

Theorem SPLIT_evm2set_EXISTS[local]:
  ∀s u v. SPLIT (evm2set s) (u,v) = ?y. (u = evm2set_on y s) /\ (v = evm2set_without y s)
Proof
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_evm2set]
  \\ gvs[SPLIT_def]
  \\ `u SUBSET (evm2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ gvs[evm2set_without_def, SUBSET_evm2set]
  \\ qexists_tac`y` \\ simp[]
  \\ gvs[EXTENSION, IN_DISJOINT]
  \\ metis_tac[]
QED

Theorem FORALL_evm_el[local] =
  DatatypeSimps.mk_type_forall_thm_tyinfo $ Option.valOf $
  TypeBase.read {Thy="vfmProg",Tyop="evm_el"}

Theorem evm2set_without_11[local]:
  !y y' s s'. (evm2set_without y' s' = evm2set_without y s) ==> (y = y')
Proof
  qsuff_tac`∀y y' s s'. evm2set_without y' s' ⊆ evm2set_without y s ⇒ y ⊆ y'`
  >- METIS_TAC[SET_EQ_SUBSET]
  \\ rw[evm2set_without_def, evm2set_def, SUBSET_DEF]
  \\ qpat_x_assum ‘!x. _’ mp_tac
  \\ simp[FORALL_evm_el]
  \\ simp[evm2set_on_def, PUSH_IN_INTO_IF]
  \\ strip_tac
  \\ Cases_on`x` \\ gvs[]
  \\ CCONTR_TAC \\ gvs[]
  \\ metis_tac[]
QED

Theorem EMPTY_evm2set[local]:
  ((evm2set_on dom s = {}) ⇔  dom = {}) ∧
  ((SEP_EQ {} (evm2set_on dom s)) ⇔ dom = {})
Proof
  simp[evm2set_on_def, PUSH_IN_INTO_IF, CaseEq"bool", SEP_EQ_def]
  \\ rw[EXTENSION, EQ_IMP_THM]
  \\ Cases_on`x` \\ rw[]
QED

(* ----------------------------------------------------------------------------- *)
(* Defining the EVM_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

Definition evm_Stack_def:
  evm_Stack s = SEP_EQ { Stack s }
End

Definition evm_GasUsed_def:
  evm_GasUsed g = SEP_EQ { GasUsed g }
End

Definition evm_MsgParams_def:
  evm_MsgParams p = SEP_EQ { MsgParams p }
End

Definition evm_TxParams_def:
  evm_TxParams t = SEP_EQ { TxParams t }
End

Definition evm_JumpDest_def:
  evm_JumpDest j = SEP_EQ { JumpDest j }
End

Definition evm_PC_def:
  evm_PC pc = SEP_EQ { PC pc }
End

Definition evm_Exception_def:
  evm_Exception x = SEP_EQ { Exception x }
End

Definition evm_Contexts_def:
  evm_Contexts x = SEP_EQ { Contexts x }
End

Definition evm_CachedRB_def:
  evm_CachedRB x = SEP_EQ { CachedRB x }
End

Definition evm_ReturnData_def:
  evm_ReturnData x = SEP_EQ { ReturnData x }
End

Definition evm_Memory_def:
  evm_Memory x = SEP_EQ { vfmProg$Memory x }
End

Definition evm_Rollback_def:
  evm_Rollback x = SEP_EQ { Rollback x }
End

Definition evm_Msdomain_def:
  evm_Msdomain x = SEP_EQ { Msdomain x }
End

Definition evm_AddRefund_def:
  evm_AddRefund x = SEP_EQ { AddRefund x }
End

Definition evm_SubRefund_def:
  evm_SubRefund x = SEP_EQ { SubRefund x }
End

Definition evm_Logs_def:
  evm_Logs x = SEP_EQ { Logs x }
End

Definition evm_Parsed_def:
  evm_Parsed pc i = SEP_EQ { Parsed pc (SOME i) T }
End

Definition evm_hide_Parsed_def:
  evm_hide_Parsed pcs = (λs.
    ∃fx fy. s = IMAGE (λpc. Parsed pc (fx pc) (fy pc)) pcs)
End

Definition EVM_NEXT_REL_def:
  EVM_NEXT_REL (s: unit execution_result) s' =
    ((if ISR (FST s) then s else step (SND s)) = s')
End

Definition EVM_INSTR_def:
  EVM_INSTR (n,op) = { Parsed n (SOME op) T }
End

Definition EVM_MODEL_def:
  EVM_MODEL = (evm2set, EVM_NEXT_REL, EVM_INSTR,
               (λx y. x = (y:unit execution_result)),
               (K F):unit execution_result -> bool)
End

(* theorems *)

Theorem evm_Parsed_CODE_POOL:
  evm_Parsed pc i = CODE_POOL EVM_INSTR {(pc,i)}
Proof
  rw[evm_Parsed_def, CODE_POOL_def, SEP_EQ_def, EVM_INSTR_def]
QED

val lemma =
  METIS_PROVE [SPLIT_evm2set]
  ``p (evm2set_on y s) ==> (?u v. SPLIT (evm2set s) (u,v) /\ p u /\ (\v. v = evm2set_without y s) v)``;

Theorem EVM_SPEC_SEMANTICS:
  SPEC EVM_MODEL p {} q =
  ∀y s seq. p (evm2set_on y s) /\ rel_sequence EVM_NEXT_REL seq s ==>
            ∃k. q (evm2set_on y (seq k)) /\ (evm2set_without y s = evm2set_without y (seq k))
Proof
  SIMP_TAC std_ss [GSYM RUN_EQ_SPEC,RUN_def,EVM_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_evm2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = evm2set_without y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_evm2set_EXISTS]
  \\ IMP_RES_TAC evm2set_without_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []
QED


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC EVM_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

Theorem STAR_evm2set:
  ((evm_PC n * p) (evm2set_on dom s) ⇔
   (n = (FST (HD (SND s).contexts)).pc) /\
   HasPC ∈ dom /\ p (evm2set_on (dom DELETE HasPC) s)) /\
  ((evm_Stack ss * p) (evm2set_on dom s) ⇔
   (ss = (FST (HD (SND s).contexts)).stack) /\
   HasStack ∈ dom /\ p (evm2set_on (dom DELETE HasStack) s)) /\
  ((evm_GasUsed g * p) (evm2set_on dom s) ⇔
   (g = (FST (HD (SND s).contexts)).gasUsed) /\
   HasGasUsed ∈ dom /\ p (evm2set_on (dom DELETE HasGasUsed) s)) /\
  ((evm_JumpDest j * p) (evm2set_on dom s) ⇔
   (j = (FST (HD (SND s).contexts)).jumpDest) /\
   HasJumpDest ∈ dom /\ p (evm2set_on (dom DELETE HasJumpDest) s)) /\
  ((evm_MsgParams p' * p) (evm2set_on dom s) ⇔
   (p' = (FST (HD (SND s).contexts)).msgParams) /\
   HasMsgParams ∈ dom /\ p (evm2set_on (dom DELETE HasMsgParams) s)) /\
  ((evm_ReturnData rd * p) (evm2set_on dom s) ⇔
   (rd = (FST (HD (SND s).contexts)).returnData) /\
   HasReturnData ∈ dom /\ p (evm2set_on (dom DELETE HasReturnData) s)) /\
  ((evm_AddRefund ad * p) (evm2set_on dom s) ⇔
   (ad = (FST (HD (SND s).contexts)).addRefund) /\
   HasAddRefund ∈ dom /\ p (evm2set_on (dom DELETE HasAddRefund) s)) /\
  ((evm_SubRefund ad * p) (evm2set_on dom s) ⇔
   (ad = (FST (HD (SND s).contexts)).subRefund) /\
   HasSubRefund ∈ dom /\ p (evm2set_on (dom DELETE HasSubRefund) s)) /\
  ((evm_Logs l * p) (evm2set_on dom s) ⇔
   (l = (FST (HD (SND s).contexts)).logs) ∧
   HasLogs ∈ dom ∧ p (evm2set_on (dom DELETE HasLogs) s)) ∧
  ((evm_Memory mem * p) (evm2set_on dom s) ⇔
   (mem = (FST (HD (SND s).contexts)).memory) /\
   HasMemory ∈ dom /\ p (evm2set_on (dom DELETE HasMemory) s)) /\
  ((evm_Rollback rb * p) (evm2set_on dom s) ⇔
   (rb = (SND s).rollback) /\
   HasRollback ∈ dom /\ p (evm2set_on (dom DELETE HasRollback) s)) /\
  ((evm_TxParams t * p) (evm2set_on dom s) ⇔
   (t = (SND s).txParams) /\
   HasTxParams ∈ dom /\ p (evm2set_on (dom DELETE HasTxParams) s)) /\
  ((evm_Msdomain d * p) (evm2set_on dom s) ⇔
   (d = (SND s).msdomain) /\
   HasMsdomain ∈ dom /\ p (evm2set_on (dom DELETE HasMsdomain) s)) /\
  ((evm_Exception e * p) (evm2set_on dom s) ⇔
   (e = FST s) /\
   HasException ∈ dom /\ p (evm2set_on (dom DELETE HasException) s)) /\
  ((evm_Contexts c * p) (evm2set_on dom s) ⇔
   (c = TL (SND s).contexts) /\
   HasContexts ∈ dom /\ p (evm2set_on (dom DELETE HasContexts) s)) /\
  ((evm_CachedRB rb * p) (evm2set_on dom s) ⇔
   (rb = SND (HD (SND s).contexts)) ∧
   HasCachedRB ∈ dom ∧ p (evm2set_on (dom DELETE HasCachedRB) s)) ∧
  ((evm_Parsed pc i * p) (evm2set_on dom s) ⇔
   (wf_state (SND s) ∧
    FLOOKUP (FST (HD (SND s).contexts)).msgParams.parsed pc = SOME i ∧
    HasParsed pc IN dom ∧
    p (evm2set_on (dom DELETE HasParsed pc) s))) ∧
  ((cond b * p) (evm2set_on dom s) ⇔
   b /\ p (evm2set_on dom s))
Proof
  simp [cond_STAR,EQ_STAR,
        evm_PC_def, evm_JumpDest_def, evm_MsgParams_def, evm_GasUsed_def,
        evm_ReturnData_def, evm_Stack_def, evm_Exception_def,
        evm_TxParams_def, evm_Contexts_def, evm_CachedRB_def, evm_Memory_def,
        evm_Rollback_def, evm_Msdomain_def, evm_Logs_def,
        evm_AddRefund_def, evm_SubRefund_def, evm_Parsed_def]
  \\ rw[EQ_IMP_THM]
  >>~- ([`pc < _ (* g *)`], gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  >>~- ([`wf_state _ (* g *)`], gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  >>~- ([`_ ∈ _ (* g *)`] , gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  >>~- ([`_ = _ (* g *)`] , gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  \\ qmatch_goalsub_abbrev_tac`p s1`
  \\ qmatch_asmsub_abbrev_tac`p s2`
  \\ `s1 = s2` suffices_by rw[]
  \\ rw[Abbr`s1`, Abbr`s2`]
  \\ gvs[evm2set_on_def, EXTENSION, PUSH_IN_INTO_IF]
  \\ rw[EQ_IMP_THM]
  \\ strip_tac \\ gvs[]
QED

Theorem STAR_evm_hide_Parsed:
  ((evm_hide_Parsed pcs * p) (evm2set_on dom s)) <=>
  (IMAGE HasParsed pcs SUBSET dom ∧
   p (evm2set_on (dom DIFF (IMAGE HasParsed pcs)) s))
Proof
  simp[evm_hide_Parsed_def, STAR_def, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  >- (
    gvs[SPLIT_def, SUBSET_DEF, PULL_EXISTS]
    \\ qx_gen_tac `pc` \\ strip_tac
    \\ Q.SUBGOAL_THEN `Parsed pc (fx pc) (fy pc) IN evm2set_on dom s` assume_tac
    >- (gvs[Once EXTENSION, PULL_EXISTS] \\ metis_tac[])
    \\ gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  >- (
    gvs[SPLIT_def, PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac`p s1`
    \\ qmatch_asmsub_abbrev_tac`p s2`
    \\ `s1 = s2` suffices_by rw[]
    \\ rw[Abbr`s1`, Abbr`s2`]
    \\ gvs[evm2set_on_def, Once EXTENSION, PUSH_IN_INTO_IF, PULL_EXISTS]
    \\ simp[Once EXTENSION, PUSH_IN_INTO_IF]
    \\ rw[Once EQ_IMP_THM]
    \\ fsrw_tac[DNF_ss][Once EQ_IMP_THM]
    >- metis_tac[]
    \\ last_x_assum drule \\ rw[]
    \\ strip_tac \\ gvs[IN_DISJOINT]
    \\ qmatch_asmsub_abbrev_tac`pa ∈ v`
    \\ first_x_assum(qspec_then`pa`mp_tac)
    \\ simp[Abbr`pa`])
  \\ first_assum $ irule_at Any
  \\ simp[SPLIT_def]
  \\ simp[evm2set_on_def, PUSH_IN_INTO_IF, Once EXTENSION,
          PULL_EXISTS, IN_DISJOINT]
  \\ gvs[SF DNF_ss, Once EQ_IMP_THM, SUBSET_DEF, IN_DISJOINT]
  \\ qmatch_goalsub_abbrev_tac`_ _ = fx _`
  \\ qexistsl_tac[`λpc. wf_state (SND s)`,`fx`]
  \\ simp[]
  \\ rw[]
  \\ spose_not_then strip_assume_tac \\ gvs[]
QED

Theorem CODE_POOL_EMPTY:
  CODE_POOL i {} = SEP_EQ {}
Proof
  rw[CODE_POOL_def, SEP_EQ_def]
QED

Theorem STAR_CODE_POOL_evm2set:
  ((CODE_POOL EVM_INSTR c * p) (evm2set_on dom s) ⇔
   IMAGE (HasParsed o FST) c SUBSET dom ∧
   (c ≠ {} ⇒ wf_state (SND s)) ∧
   (∀pc i. (pc,i) ∈ c ⇒
      FLOOKUP (FST (HD (SND s).contexts)).msgParams.parsed pc = SOME i) ∧
   p (evm2set_on (dom DIFF IMAGE (HasParsed o FST) c) s))
Proof
  rw[Once EXTENSION, SUBSET_DEF, PULL_EXISTS, STAR_def, SPLIT_def,
     FORALL_PROD]
  \\ simp[Once EQ_IMP_THM, CODE_POOL_def, PULL_EXISTS, EVM_INSTR_def,
          IN_DISJOINT, EXISTS_PROD]
  \\ conj_tac
  >- (
    ntac 2 strip_tac
    \\ simp[PULL_FORALL]
    \\ gvs[Once EQ_IMP_THM, PULL_EXISTS, SF DNF_ss]
    \\ last_x_assum mp_tac \\ simp[Once evm2set_on_def, PUSH_IN_INTO_IF]
    \\ strip_tac
    \\ conj_tac >- metis_tac[]
    \\ simp[Once EXTENSION, EXISTS_PROD, PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac`p v2`
    \\ `v2 = v` suffices_by rw[]
    \\ simp[Abbr`v2`, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ reverse conj_tac
    >- (
        rw[]
        \\ first_x_assum drule
        \\ simp[evm2set_on_def, PUSH_IN_INTO_IF]
        \\ rw[FORALL_PROD]
        \\ rpt strip_tac
        \\ first_x_assum drule
        \\ strip_tac
        \\ qmatch_asmsub_abbrev_tac`x ∈ v`
        \\ first_x_assum(qspec_then`x`mp_tac)
        \\ simp[Abbr`x`]
        \\ metis_tac[])
     \\ qpat_x_assum`!x. x ∈ _ ⇒ _`mp_tac
     \\ simp[evm2set_on_def, PUSH_IN_INTO_IF]
     \\ rw[] \\ gvs[]
     \\ qmatch_goalsub_abbrev_tac`x ∈ v`
     \\ first_x_assum(qspec_then`x`mp_tac) \\ simp[Abbr`x`])
  \\ strip_tac
  \\ first_assum $ irule_at Any
  \\ reverse conj_tac
  >- (
    Cases \\ simp[Once evm2set_on_def, PUSH_IN_INTO_IF, EXISTS_PROD]
    \\ rpt strip_tac \\ gvs[]
    \\ spose_not_then strip_assume_tac
    \\ metis_tac[])
  \\ Cases \\ simp[Once evm2set_on_def, PUSH_IN_INTO_IF]
  \\ simp[Once evm2set_on_def, PUSH_IN_INTO_IF, FORALL_PROD]
  \\ gs[Once EXTENSION, EXISTS_PROD, PULL_EXISTS]
  \\ rw[Once EQ_IMP_THM]
  \\ metis_tac[]
QED

Theorem FLOOKUP_parse_code_0[local,simp]:
  FLOOKUP (parse_code 0 FEMPTY code) pc = SOME i ⇒
  ¬(LENGTH code ≤ pc)
Proof
  strip_tac \\ drule FLOOKUP_parse_code_SOME_less_LENGTH \\ rw[NOT_LESS_EQUAL]
QED

val CODE_POOL_evm2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) ⇔ (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

Theorem CODE_POOL_evm2set:
  CODE_POOL EVM_INSTR {(p,c)} (evm2set_on dom s) ⇔
    dom = {HasParsed p} ∧
    FLOOKUP (FST (HD (SND s).contexts)).msgParams.parsed p = SOME c ∧
    wf_state (SND s)
Proof
  rw[CODE_POOL_def, EVM_INSTR_def]
  \\ simp[evm2set_on_def, EXTENSION, PUSH_IN_INTO_IF]
  \\ EQ_TAC \\ strip_tac
  >- (
    gvs[FORALL_evm_el]
    \\ first_assum(qspecl_then[`p`,`SOME c`,`T`]mp_tac)
    \\ simp_tac (srw_ss()) []
    \\ strip_tac
    \\ Cases \\ simp[] \\ CCONTR_TAC \\ gvs[]
    \\ fsrw_tac[DNF_ss][EQ_IMP_THM]
    \\ metis_tac[] )
  \\ Cases \\ simp[]
  \\ rw[EQ_IMP_THM]
QED

Theorem UPDATE_evm2set_without[local]:
  wf_state s ∧
  ctxt = FST (HD s.contexts) ∧
  s' = SND r' ∧ s = SND r ∧
  wf_state s' ∧
  ctxt' = FST (HD s'.contexts) ∧
  (HasException ∉ dom ⇒ FST r' = FST r) ∧
  (HasStack ∉ dom ⇒ ctxt'.stack = ctxt.stack) ∧
  (HasGasUsed ∉ dom ⇒ ctxt'.gasUsed = ctxt.gasUsed) ∧
  (HasMsgParams ∉ dom ⇒ ctxt'.msgParams = ctxt.msgParams) ∧
  (HasLogs ∉ dom ⇒ ctxt'.logs = ctxt.logs) ∧
  (HasSubRefund ∉ dom ⇒ ctxt'.subRefund = ctxt.subRefund) ∧
  (HasAddRefund ∉ dom ⇒ ctxt'.addRefund = ctxt.addRefund) ∧
  (HasReturnData ∉ dom ⇒ ctxt'.returnData = ctxt.returnData) ∧
  (HasJumpDest ∉ dom ⇒ ctxt'.jumpDest = ctxt.jumpDest) ∧
  (HasMemory ∉ dom ⇒ ctxt'.memory = ctxt.memory) ∧
  (HasPC ∉ dom ⇒ ctxt'.pc = ctxt.pc) ∧
  (∀pc. HasParsed pc ∉ dom ⇒
        ((*(pc < LENGTH ctxt'.msgParams.code <=> pc < LENGTH ctxt.msgParams.code) ∧*)
         (FLOOKUP ctxt'.msgParams.parsed pc = FLOOKUP ctxt.msgParams.parsed pc))) ∧
  (HasContexts ∉ dom ⇒ TL s'.contexts = TL s.contexts) ∧
  (HasCachedRB ∉ dom ⇒ SND (HD s'.contexts) = SND (HD s.contexts)) ∧
  (HasTxParams ∉ dom ⇒ s'.txParams = s.txParams) ∧
  (HasRollback ∉ dom ⇒ s'.rollback = s.rollback) ∧
  (HasMsdomain ∉ dom ⇒ s'.msdomain = s.msdomain)
  ⇒
  evm2set_without dom r' = evm2set_without dom r
Proof
  disch_then assume_tac
  \\ simp[evm2set_without_def]
  \\ simp[evm2set_def, EXTENSION]
  \\ simp[evm2set_on_def]
  \\ Cases \\ simp[PUSH_IN_INTO_IF]
  \\ rw[Once EQ_IMP_THM] \\ gvs[]
QED

val V_SPEC_CODE =
  SPEC_CODE |> ISPEC ``EVM_MODEL``
  |> SIMP_RULE std_ss [EVM_MODEL_def]
  |> REWRITE_RULE [GSYM EVM_MODEL_def];

Theorem IMP_EVM_SPEC_LEMMA[local]:
  ∀p q.
    (∀s dom.
       ∃s'.
         (p (evm2set_on dom s) ==>
          ((if ISR (FST s) then s else step (SND s)) = s') /\
           q (evm2set_on dom s') /\
          (evm2set_without dom s = evm2set_without dom s'))) ==>
    SPEC EVM_MODEL p {} q
Proof
  SIMP_TAC std_ss [RIGHT_EXISTS_IMP_THM] \\ REWRITE_TAC [EVM_SPEC_SEMANTICS]
  \\ SIMP_TAC std_ss [FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,EVM_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0`
  \\ first_x_assum $ qspec_then ‘0’ mp_tac
  \\ fs [] \\ rw [] \\ fs[] \\ gvs[quantHeuristicsTheory.ISL_exists]
QED

Theorem IMP_EVM_SPEC =
  (ONCE_REWRITE_RULE [STAR_COMM] o REWRITE_RULE [V_SPEC_CODE] o
   SPECL [``CODE_POOL EVM_INSTR c * p'``,
          ``CODE_POOL EVM_INSTR c * q'``]) IMP_EVM_SPEC_LEMMA;

(*-------------------------------------------------------------------------------*
   Theorems for lifting SPEC triples to the run level
 *-------------------------------------------------------------------------------*)

Theorem rel_sequence_EVM_NEXT_REL_FUNPOW:
  rel_sequence EVM_NEXT_REL seq s =
  ∀n. seq n = FUNPOW (λs. if ISR(FST s) then s else step (SND s)) n s
Proof
  rw[rel_sequence_def, EVM_NEXT_REL_def, EQ_IMP_THM, FUNPOW_SUC]
  \\ Induct_on`n`
  \\ rw[FUNPOW_SUC]
  \\ metis_tac[]
QED

Theorem run_tr_rel_sequence_EVM_NEXT_REL:
  ∀r1a r1d r2a r2d.
  run_tr (r1a, r1d) = (r2a, r2d) ⇒
  ∃seq k. rel_sequence EVM_NEXT_REL seq (r1a, r1d) ∧
          (∀j. k ≤ j ⇒ seq j = (INR r2a, r2d)) ∧
          (∀j. j < k ⇒ ISL (FST (seq j)))
Proof
  ho_match_mp_tac run_tr_ind
  \\ rpt gen_tac \\ strip_tac
  \\ simp[Once run_tr_def]
  \\ gvs[rel_sequence_EVM_NEXT_REL_FUNPOW, GSYM FUN_EQ_THM]
  \\ reverse CASE_TAC >- (
    qexists_tac`0` \\ rw[FUNPOW_SUC] \\
    Induct_on`j` \\ rw[FUNPOW])
  \\ rw[] \\ gvs[]
  \\ qexists_tac`SUC k`
  \\ conj_tac >- ( Induct \\ gvs[FUNPOW] )
  \\ Cases \\ gvs[FUNPOW]
QED

Theorem run_rel_sequence_EVM_NEXT_REL:
  ∃x r2 seq k.
    run s1 = SOME (INR x, r2) ∧
    rel_sequence EVM_NEXT_REL seq (step s1) ∧
    (∀j. k ≤ j ⇒ seq j = (INR x, r2)) ∧
    (∀j. j < k ⇒ ISL (FST (seq j)))
Proof
  rw[run_eq_tr]
  \\ Cases_on`step s1`
  \\ CASE_TAC
  \\ irule run_tr_rel_sequence_EVM_NEXT_REL
  \\ rw[]
QED

Theorem run_from_SPEC:
  SPEC EVM_MODEL P {} Q ∧ P (evm2set (INL (), s1)) ∧
  (Q = evm_Exception (INR x) * R)
  ⇒ ∃rs2. run s1 = SOME rs2 ∧ Q (evm2set rs2)
Proof
  simp[EVM_SPEC_SEMANTICS, rel_sequence_EVM_NEXT_REL_FUNPOW, evm2set_def]
  \\ strip_tac
  \\ first_x_assum drule
  \\ simp[GSYM FUN_EQ_THM]
  \\ strip_tac
  \\ goal_assum $ drule_at Any
  \\ strip_assume_tac run_rel_sequence_EVM_NEXT_REL
  \\ gvs[rel_sequence_EVM_NEXT_REL_FUNPOW]
  \\ Cases_on`k` \\ gvs[]
  >- gvs[STAR_evm2set]
  \\ gvs[FUNPOW]
  \\ qmatch_asmsub_rename_tac `k ≤ _`
  \\ Cases_on `k ≤ n` \\ gvs[NOT_LESS_EQUAL]
  \\ first_x_assum drule
  \\ gvs[STAR_evm2set]
  \\ qpat_x_assum`INR _ = _`(mp_tac o SYM) \\ rw[]
QED

(*-------------------------------------------------------------------------------*
   Bridging theorem: SPEC to run_transaction
 *-------------------------------------------------------------------------------*)

(* Helper: extract returnData from SPEC postcondition *)
Theorem extract_returnData_from_SPEC_postcondition:
  (evm_Exception (INR NONE) * evm_ReturnData rd * evm_Contexts [] * R)
    (evm2set rs) ∧
  (SND rs).contexts ≠ []
  ⇒
  FST rs = INR NONE ∧
  TL (SND rs).contexts = [] ∧
  (FST (HD (SND rs).contexts)).returnData = rd
Proof
  simp[evm2set_def]
  \\ rewrite_tac[GSYM STAR_ASSOC, STAR_evm2set]
  \\ simp[]
QED

(* Lemma: initial_state sets callee correctly *)
Theorem initial_state_callee:
  initial_state dom static chainId prevHashes blk accounts tx = SOME s ∧
  tx.to = SOME callee
  ⇒
  (FST (HD s.contexts)).msgParams.callee = callee
Proof
  rw[initial_state_def,CaseEq"option"]
  \\ pairarg_tac \\ gvs[]
  \\ pairarg_tac \\ gvs[CaseEq"option"]
  \\ gvs[apply_intrinsic_cost_def]
  \\ rw[initial_msg_params_def]
  \\ rw[callee_from_tx_to_def]
QED

(* Lemma: run_create for message calls to non-precompiles *)
Theorem run_create_call:
  initial_state dom static chainId prevHashes blk accounts tx = SOME s ∧
  tx.to = SOME callee ∧
  ¬fIN callee precompile_addresses
  ⇒
  run_create dom static chainId prevHashes blk accounts tx =
  SOME (INR (s.rollback.accounts,
             s with rollback updated_by
               (λr. r with accounts updated_by
                  transfer_value tx.from callee tx.value),
             NONE))
Proof
  rw[run_create_def]
  \\ imp_res_tac initial_state_callee
  \\ gvs[]
QED

(* Lemma: post_transaction_accounting extracts output and logs correctly on success *)
Theorem post_transaction_accounting_success:
  ¬NULL t.contexts ∧
  NULL (TL t.contexts)
  ⇒
  (FST (post_transaction_accounting blk tx NONE acc t)).result = NONE ∧
  (FST (post_transaction_accounting blk tx NONE acc t)).output =
    (FST (HD t.contexts)).returnData ∧
  (FST (post_transaction_accounting blk tx NONE acc t)).logs =
    (FST (HD t.contexts)).logs
Proof
  qmatch_goalsub_abbrev_tac`FST pta`
  \\ pop_assum mp_tac
  \\ rewrite_tac[post_transaction_accounting_def]
  \\ qmatch_goalsub_abbrev_tac`_ ⇒ conc`
  \\ BasicProvers.LET_ELIM_TAC
  \\ gvs[Abbr`conc`, NULL_EQ, Abbr`pta`,Abbr`tr`]
  \\ strip_tac \\ gvs[]
QED

(* Lemma: initial_state produces a state with nonempty contexts *)
Theorem initial_state_nonempty_contexts:
  initial_state dom static chainId prevHashes blk accounts tx = SOME s
  ⇒
  s.contexts ≠ []
Proof
  rw[initial_state_def, CaseEq"option"]
  \\ pairarg_tac \\ gvs[]
  \\ pairarg_tac \\ gvs[CaseEq"option"]
QED

(* Lemma: lookup_account is preserved by update_account for other addresses *)
Theorem lookup_account_update_account_other:
  addr ≠ addr' ⇒
  lookup_account addr (update_account addr' v acc) = lookup_account addr acc
Proof
  rw[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

(* Lemma: lookup_account returns the updated value for the same address *)
Theorem lookup_account_update_account_same:
  lookup_account addr (update_account addr v acc) = v
Proof
  rw[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

(* Lemma: lookup_account is preserved by process_deletions for non-deleted addresses *)
Theorem lookup_account_process_deletions_other:
  ¬MEM addr toDelete ⇒
  lookup_account addr (process_deletions toDelete acc) = lookup_account addr acc
Proof
  qid_spec_tac `acc`
  \\ Induct_on `toDelete`
  >- rw[process_deletions_def]
  >- (rw[process_deletions_def] \\ simp[lookup_account_update_account_other])
QED

(* Lemma: deleted addresses become empty_account_state *)
Theorem lookup_account_process_deletions_deleted:
  MEM addr toDelete ⇒
  lookup_account addr (process_deletions toDelete acc) = empty_account_state
Proof
  qid_spec_tac `acc`
  \\ Induct_on `toDelete`
  >- rw[]
  >- (rw[process_deletions_def]
      >- (Cases_on `MEM addr toDelete`
          >- (first_x_assum irule \\ first_x_assum ACCEPT_TAC)
          >- simp[lookup_account_process_deletions_other,
                  lookup_account_update_account_same])
      >- (first_x_assum irule \\ first_x_assum ACCEPT_TAC))
QED

(* Lemma: post_transaction_accounting preserves accounts for addresses
   not involved in gas accounting *)
Theorem post_transaction_accounting_accounts:
  ¬NULL t.contexts ∧
  NULL (TL t.contexts) ∧
  addr ≠ tx.from ∧
  addr ≠ blk.coinBase ∧
  ¬MEM addr t.rollback.toDelete
  ⇒
  lookup_account addr (SND (post_transaction_accounting blk tx NONE acc t)) =
  lookup_account addr t.rollback.accounts
Proof
  rewrite_tac[post_transaction_accounting_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ gvs[]
  \\ simp[Abbr`newAccounts`, lookup_account_update_account_other]
  \\ simp[Abbr`accounts`, lookup_account_process_deletions_other]
QED

(* Helper definitions for gas accounting in bridging theorem *)
Definition compute_gas_left_def:
  compute_gas_left (ctxtGasLimit:num) ctxtGasUsed = ctxtGasLimit - ctxtGasUsed
End

Definition compute_tx_gas_used_def:
  compute_tx_gas_used (txGasLimit:num) ctxtGasLimit ctxtGasUsed =
    txGasLimit - compute_gas_left ctxtGasLimit ctxtGasUsed
End

Definition compute_total_gas_used_def:
  compute_total_gas_used (txGasLimit:num) txData ctxtGasLimit ctxtGasUsed
                         ctxtAddRefund ctxtSubRefund authRefund =
    let txGasUsed = compute_tx_gas_used txGasLimit ctxtGasLimit ctxtGasUsed in
    let storageRefund = ctxtAddRefund - ctxtSubRefund in
    let gasRefund = MIN (txGasUsed DIV 5) (authRefund + storageRefund) in
    let floor_cost = calldata_floor_cost txData in
      MAX (txGasUsed - gasRefund) floor_cost
End

Definition compute_refund_ether_def:
  compute_refund_ether (txGasLimit:num) txGasPrice txData ctxtGasLimit ctxtGasUsed
                       ctxtAddRefund ctxtSubRefund authRefund =
    let totalGasUsed = compute_total_gas_used txGasLimit txData ctxtGasLimit
                         ctxtGasUsed ctxtAddRefund ctxtSubRefund authRefund in
      (txGasLimit - totalGasUsed) * txGasPrice
End

Definition compute_transaction_fee_def:
  compute_transaction_fee (txGasLimit:num) txGasPrice baseFeePerGas txData
                          ctxtGasLimit ctxtGasUsed ctxtAddRefund ctxtSubRefund
                          authRefund =
    let totalGasUsed = compute_total_gas_used txGasLimit txData ctxtGasLimit
                         ctxtGasUsed ctxtAddRefund ctxtSubRefund authRefund in
    let priorityFeePerGas = txGasPrice - baseFeePerGas in
      totalGasUsed * priorityFeePerGas
End

(* Main bridging theorem: connects SPEC to run_transaction for message calls *)
Theorem SPEC_to_run_transaction:
  (* SPEC preconditions *)
  SPEC EVM_MODEL P {} Q ∧
  (* Transaction is a message call to a non-precompile *)
  tx.to = SOME callee ∧
  ¬fIN callee precompile_addresses ∧
  (* Well-formed accounts *)
  wf_accounts accounts ∧
  (* initial_state succeeds *)
  initial_state dom F chainId prevHashes blk accounts tx = SOME s ∧
  (* The state after transfer_value modification satisfies precondition P *)
  s' = s with rollback updated_by
       (λr. r with accounts updated_by transfer_value tx.from callee tx.value) ∧
  P (evm2set (INL (), s')) ∧
  (* Postcondition has the required form for successful execution *)
  Q = evm_Exception (INR NONE) * evm_ReturnData returnData *
      evm_Logs logs * evm_Rollback rb * evm_Contexts [] *
      evm_GasUsed gasUsed * evm_MsgParams msgParams *
      evm_AddRefund addRefund * evm_SubRefund subRefund *
      evm_TxParams txParams * R
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = returnData ∧
    result.logs = logs ∧
    (* Full account specification *)
    (let acc_del = process_deletions rb.toDelete rb.accounts;
         sender = lookup_account tx.from acc_del;
         coinbase = lookup_account blk.coinBase acc_del;
         refundEther = compute_refund_ether tx.gasLimit tx.gasPrice tx.data
                         msgParams.gasLimit gasUsed addRefund subRefund
                         txParams.authRefund;
         transactionFee = compute_transaction_fee tx.gasLimit tx.gasPrice
                            blk.baseFeePerGas tx.data msgParams.gasLimit gasUsed
                            addRefund subRefund txParams.authRefund
     in
       (* tx.from gets refund added to balance *)
       lookup_account tx.from accounts' =
         sender with balance := sender.balance + refundEther ∧
       (* blk.coinBase gets fee added (when different from tx.from) *)
       (tx.from ≠ blk.coinBase ⇒
         lookup_account blk.coinBase accounts' =
           coinbase with balance := coinbase.balance + transactionFee) ∧
       (* All other addresses: same as after deletions *)
       (∀addr. addr ≠ tx.from ∧ addr ≠ blk.coinBase ⇒
         lookup_account addr accounts' = lookup_account addr acc_del))
Proof
  strip_tac
  \\ simp[run_transaction_def]
  \\ `run_create dom F chainId prevHashes blk accounts tx =
      SOME (INR (s.rollback.accounts, s', NONE))`
       by (imp_res_tac run_create_call >> gvs[])
  \\ simp[]
  \\ sg `∃rs2. run s' = SOME rs2 ∧ Q (evm2set rs2)`
  >- (irule run_from_SPEC
      \\ conj_tac
      >- (qexists_tac `evm_ReturnData returnData * evm_Logs logs *
            evm_Rollback rb * evm_Contexts [] * evm_GasUsed gasUsed *
            evm_MsgParams msgParams * evm_AddRefund addRefund *
            evm_SubRefund subRefund * evm_TxParams txParams * R`
          \\ qexists_tac `NONE` \\ gvs[] \\ simp[STAR_ASSOC])
      >- (qexists_tac `P` \\ simp[]))
  >- (gvs[]
      \\ sg `FST rs2 = INR NONE`
      >- (qpat_x_assum `(_ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _) _` mp_tac
          \\ simp[evm2set_def]
          \\ rewrite_tac[GSYM STAR_ASSOC, STAR_evm2set]
          \\ simp[])
      >- (Cases_on `rs2` \\ gvs[]
          \\ sg `r.contexts <> []`
          >- (`s.contexts <> []` by (drule initial_state_nonempty_contexts >> simp[])
              \\ `(s with rollback updated_by _).contexts = s.contexts` by simp[]
              \\ imp_res_tac run_preserves_nonempty_contexts \\ gvs[])
          >- (qpat_x_assum `(_ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _) _` mp_tac
              \\ simp[evm2set_def, STAR_evm2set]
              \\ rewrite_tac[GSYM STAR_ASSOC, STAR_evm2set]
              \\ simp[]
              \\ strip_tac
              \\ Cases_on `post_transaction_accounting blk tx NONE
                           s.rollback.accounts r`
              \\ qexistsl_tac [`q`, `r''`]
              \\ simp[]
              \\ `~(NULL r.contexts \/ ~NULL (TL r.contexts))` by gvs[NULL_EQ]
              \\ qabbrev_tac `ctxt = FST (HD r.contexts)`
              \\ qabbrev_tac `acc_del = process_deletions
                              r.rollback.toDelete r.rollback.accounts`
              \\ qpat_x_assum `post_transaction_accounting _ _ _ _ _ = _`
                   (strip_assume_tac o
                    ONCE_REWRITE_RULE[post_transaction_accounting_def])
              \\ gvs[compute_refund_ether_def, compute_transaction_fee_def,
                     compute_total_gas_used_def, compute_tx_gas_used_def,
                     compute_gas_left_def]
              \\ simp[lookup_account_update_account_same,
                      lookup_account_update_account_other]
              \\ Cases_on `lookup_account tx.from acc_del`
              \\ simp[]
              \\ rw[]
              >- simp[vfmStateTheory.recordtype_account_state_seldef_balance_fupd_def]
              >- (Cases_on `lookup_account blk.coinBase acc_del`
                  \\ simp[vfmStateTheory.recordtype_account_state_seldef_balance_fupd_def]))))
QED

(*-------------------------------------------------------------------------------*
   Hoare triples for specific opcodes
 *-------------------------------------------------------------------------------*)

(* TODO: move? *)

Theorem access_address_contexts_unchanged:
  access_address a s = (r,t) ⇒
  t.contexts = s.contexts
Proof
  rw[access_address_def, domain_check_def]
  \\ pop_assum mp_tac \\ CASE_TAC
  \\ rw[return_def, fail_def, set_domain_def, bind_def, ignore_bind_def]
  \\ rw[]
QED

Definition with_zero_mod_def:
  with_zero_mod f (x:bytes32) (y:bytes32) (n:bytes32) =
  if n = 0w then (0w:bytes32) else n2w (f (w2n x) (w2n y) MOD (w2n n))
End

Definition exponent_byte_size_def:
  exponent_byte_size (w:bytes32) =
  if w = 0w then 0 else SUC (LOG2 (w2n w) DIV 8)
End

Definition exp_cost_def:
  exp_cost w = static_gas Exp + exp_per_byte_cost * exponent_byte_size w
End

Definition msdomain_add_def:
  msdomain_add a d =
  case d of Enforce _ => d
          | Collect x => Collect $ x with addresses updated_by fINSERT a
End

Definition accesses_add_def:
  accesses_add a rb =
  rb with accesses updated_by
  (λx. x with addresses updated_by fINSERT a)
End

Theorem accesses_add_accounts[simp]:
  (accesses_add a rb).accounts = rb.accounts
Proof
  rw[accesses_add_def]
QED

Definition access_cost_def:
  access_cost rb a =
  if fIN a rb.accesses.addresses then warm_access_cost else cold_access_cost
End

Definition access_check_def:
  access_check d a =
  case d of Enforce x => fIN a x.addresses
  | Collect _ => T
End

Theorem access_address_split:
  access_check s.msdomain a ⇒
  access_address a s =
  (INL (access_cost s.rollback a),
   s with <| rollback updated_by accesses_add a
           ; msdomain updated_by msdomain_add a
           |>)
Proof
  simp[access_address_def, domain_check_def]
  \\ Cases_on `s.msdomain`
  \\ simp[access_check_def, return_def, bind_def, ignore_bind_def,
          access_cost_def, set_domain_def, msdomain_add_def,
          accesses_add_def, access_sets_component_equality,
          execution_state_component_equality,
          rollback_state_component_equality]
QED

Definition msdomain_add_slot_def:
  msdomain_add_slot a d =
  case d of Enforce _ => d
          | Collect x => Collect $ x with storageKeys updated_by fINSERT a
End

Theorem msdomain_add_slot_idem[simp]:
  msdomain_add_slot k (msdomain_add_slot k d) =
  msdomain_add_slot k d
Proof
  rw[msdomain_add_slot_def]
  \\ CASE_TAC \\ simp[domain_component_equality]
QED

Definition accesses_add_slot_def:
  accesses_add_slot sk rb =
  rb with accesses updated_by
  (λx. x with storageKeys updated_by fINSERT sk)
End

Theorem accesses_add_slot_idem[simp]:
  accesses_add_slot k (accesses_add_slot k d) =
  accesses_add_slot k d
Proof
  rw[accesses_add_slot_def]
  \\ simp[rollback_state_component_equality, access_sets_component_equality]
QED

Theorem accesses_add_slot_accounts[simp]:
  (accesses_add_slot a rb).accounts = rb.accounts
Proof
  rw[accesses_add_slot_def]
QED

Definition access_slot_cost_def:
  access_slot_cost rb a =
  if fIN a rb.accesses.storageKeys then warm_access_cost else cold_sload_cost
End

Definition access_slot_check_def:
  access_slot_check d a =
  case d of Enforce x => fIN a x.storageKeys
  | Collect _ => T
End

Theorem access_slot_split:
  access_slot_check s.msdomain a ⇒
  access_slot a s =
  (INL (access_slot_cost s.rollback a),
   s with <| rollback updated_by accesses_add_slot a
           ; msdomain updated_by msdomain_add_slot a
           |>)
Proof
  simp[access_slot_def, domain_check_def]
  \\ Cases_on `s.msdomain`
  \\ simp[access_slot_check_def, return_def, bind_def, ignore_bind_def,
          access_slot_cost_def, set_domain_def, msdomain_add_slot_def,
          accesses_add_slot_def, access_sets_component_equality,
          execution_state_component_equality,
          rollback_state_component_equality]
QED

Theorem access_slot_check_msdomain_add_slot[simp]:
  access_slot_check (msdomain_add_slot k' d) k =
  access_slot_check d k
Proof
  rw[access_slot_check_def, msdomain_add_slot_def]
  \\ CASE_TAC \\ simp[]
QED

Definition access_storage_check_def:
  access_storage_check d a =
  case d of Enforce x => fIN a x.fullStorages
  | Collect _ => T
End

Definition msdomain_add_storage_def:
  msdomain_add_storage a d =
  case d of Enforce _ => d
  | Collect x => Collect (x with fullStorages updated_by fINSERT a)
End

Theorem access_storage_split:
  access_storage_check s.msdomain a ⇒
  ensure_storage_in_domain a s =
  (INL (),
   s with msdomain updated_by msdomain_add_storage a)
Proof
  rw[ensure_storage_in_domain_def, access_storage_check_def,
     domain_check_def, set_domain_def, ignore_bind_def, bind_def, return_def]
  \\ CASE_TAC \\ gvs[execution_state_component_equality, msdomain_add_storage_def]
QED

Theorem access_storage_check_msdomain_add[simp]:
  access_storage_check (msdomain_add a d) =
  access_storage_check d
Proof
  rw[FUN_EQ_THM, access_storage_check_def, msdomain_add_def]
  \\ CASE_TAC \\ rw[]
QED

Definition memory_cost_def:
  memory_cost (m: buffer) offset size =
  memory_expansion_cost (buffer_length m)
    (if 0 < size then word_size (offset + size) * 32 else 0)
End

Theorem memory_cost_offset_to_0:
  0 < sz ⇒
  memory_cost m off sz = memory_cost m 0 (off + sz)
Proof
  rw[memory_cost_def]
QED

Theorem memory_cost_none_zero:
  32 * word_size (a + b) ≤ buffer_length m ⇒
  memory_cost m a b = 0
Proof
  rw[memory_cost_def, memory_expansion_cost_def]
  \\ rw[MAX_DEF]
QED

Theorem memory_cost_buffer_write:
  off + LENGTH bs ≤ buffer_length m ⇒
  memory_cost (buffer_write off bs m) i n = memory_cost m i n
Proof
  rw[memory_cost_def] \\ gvs[MAX_DEF]
QED

Definition memory_expand_by_def:
  memory_expand_by (m: buffer) offset size =
  MAX (buffer_length m) (if 0 < size then word_size (offset + size) * 32 else 0)
  - (buffer_length m)
End

Definition expanded_memory_def:
  expanded_memory (m: buffer) offset size =
  buffer_extend (memory_expand_by m offset size) m
End

Theorem memory_expansion_info_split:
  s.contexts ≠ [] ⇒
  memory_expansion_info offset sz s =
  (INL <| cost := memory_cost (FST (HD s.contexts)).memory offset sz;
          expand_by := memory_expand_by (FST (HD s.contexts)).memory offset sz
        |>, s)
Proof
  rw[memory_expansion_info_def, bind_def, ignore_bind_def,
     get_current_context_def, return_def, memory_cost_def,
     memory_expand_by_def]
QED

Theorem expand_memory_split:
  s.contexts ≠ [] ∧ m = (FST (HD s.contexts)).memory ⇒
  expand_memory (memory_expand_by m offset sz) s =
  (INL (), s with contexts := (
    FST (HD s.contexts) with
    memory := expanded_memory m offset sz,
    SND (HD s.contexts))::(TL s.contexts))
Proof
  rw[expand_memory_def, bind_def, ignore_bind_def, get_current_context_def,
     return_def, set_current_context_def, execution_state_component_equality,
     context_component_equality, expanded_memory_def]
QED

Theorem TAKE_expanded_memory_leq[simp]:
  n ≤ buffer_length m ⇒
  TAKE n (buffer_to_list (expanded_memory m offset sz)) =
  TAKE n (buffer_to_list m)
Proof
  rw[expanded_memory_def, buffer_to_list_extend, TAKE_APPEND1]
QED

Theorem DROP_size_expanded_memory:
  32 * word_size (offset + sz) ≤ n ⇒
  DROP n (buffer_to_list (expanded_memory m offset sz)) =
  DROP n (buffer_to_list m)
Proof
  rw[expanded_memory_def, buffer_to_list_extend, DROP_APPEND]
  \\ gvs[memory_expand_by_def, word_size_def]
QED

Theorem LENGTH_expanded_memory_geq:
  (sz = 0 ⇒ 32 * word_size off ≤ buffer_length m) ⇒
  32 * word_size (off + sz) ≤ buffer_length (expanded_memory m off sz)
Proof
  Cases_on`sz = 0` \\ gvs[]
  \\ rw[expanded_memory_def, memory_expand_by_def]
  \\ rw[MAX_DEF]
QED

Theorem expanded_memory_0[simp]:
  expanded_memory m off 0 = m
Proof
  rw[expanded_memory_def, memory_expand_by_def]
QED

Theorem buffer_length_expanded_memory:
  buffer_length (expanded_memory m off sz) =
  MAX (buffer_length m) (if 0 < sz then 32 * word_size (off + sz) else 0)
Proof
  rw[expanded_memory_def, memory_expand_by_def, MAX_DEF]
QED

Theorem buffer_take_expanded_memory:
  i + n ≤ buffer_length m ⇒
  buffer_take i n (expanded_memory m off sz) = buffer_take i n m
Proof
  rw[buffer_take_to_list, expanded_memory_def, buffer_to_list_extend,
     rich_listTheory.TAKE_DROP_SWAP, TAKE_APPEND1]
QED

Definition Keccak256_gas_def:
  Keccak256_gas m offset size =
    static_gas Keccak256 +
    memory_cost m offset size +
    keccak256_per_word_cost * word_size size
End

Definition CallDataCopy_gas_def:
  CallDataCopy_gas m offset size =
    static_gas CallDataCopy +
    memory_copy_cost * (word_size size) +
    memory_cost m offset size
End

Definition CodeCopy_gas_def:
  CodeCopy_gas m offset size =
    static_gas CodeCopy +
    memory_copy_cost * (word_size size) +
    memory_cost m offset size
End

Definition ReturnDataCopy_gas_def:
  ReturnDataCopy_gas m offset size =
    static_gas ReturnDataCopy +
    memory_copy_cost * (word_size size) +
    memory_cost m offset size
End

Definition MCopy_gas_def:
  MCopy_gas m xOffset xSize sz =
  static_gas MCopy +
  memory_copy_cost * word_size sz +
  memory_cost m xOffset xSize
End

Definition Balance_gas_def:
  Balance_gas rb a =
  static_gas Balance + access_cost rb a
End

Definition ExtCodeSize_gas_def:
  ExtCodeSize_gas rb a =
  static_gas ExtCodeSize + access_cost rb a
End

Definition ExtCodeCopy_gas_def:
  ExtCodeCopy_gas m rb a offset size =
    static_gas ExtCodeCopy +
    access_cost rb a +
    memory_copy_cost * (word_size size) +
    memory_cost m offset size
End

Definition ExtCodeHash_gas_def:
  ExtCodeHash_gas rb a =
    static_gas ExtCodeHash + access_cost rb a
End

Definition sstore_refund_updates_def:
  sstore_refund_updates originalValue currentValue (value:bytes32) =
     if currentValue ≠ value then
       let storageSetRefund =
         if originalValue = value then
           if originalValue = 0w then
             storage_set_cost - warm_access_cost
           else storage_update_cost - cold_sload_cost - warm_access_cost
         else 0
       in if originalValue ≠ 0w ∧ currentValue ≠ 0w ∧ value = 0w
          then (storageSetRefund + storage_clear_refund,0)
          else if originalValue ≠ 0w ∧ currentValue = 0w
          then (storageSetRefund,storage_clear_refund)
          else (storageSetRefund,0)
     else (0,0)
End

Definition sstore_base_gas_def:
  sstore_base_gas originalValue currentValue (value:bytes32) =
    if originalValue = currentValue ∧ currentValue ≠ value
    then if originalValue = 0w then storage_set_cost
    else storage_update_cost - cold_sload_cost
    else warm_access_cost
End

Definition SStore_gas_def:
  SStore_gas original rb address key value = let
    accounts = rb.accounts;
    account = lookup_account address accounts;
    orig_account = lookup_account address original;
    currentValue = lookup_storage key account.storage;
    originalValue = lookup_storage key orig_account.storage;
    baseDynamicGas = sstore_base_gas originalValue currentValue value;
    accessCost = access_slot_cost rb (SK address key);
    dynamicGas = baseDynamicGas + zero_warm accessCost;
    (add,sub) = sstore_refund_updates originalValue currentValue value;
  in (dynamicGas, add, sub)
End

Definition sstore_write_accounts_updater_def:
  sstore_write_accounts_updater address key value = (λaccounts.
    let account = lookup_account address accounts in
    let newAccount = account with storage updated_by update_storage key value
  in update_account address newAccount accounts)
End

Definition SStore_write_def:
  SStore_write address key value rb =
  rb with accounts updated_by
    sstore_write_accounts_updater address key value
End

Theorem rollback_with_tStorage_simp:
  (rb with tStorage updated_by g =
   rb with tStorage := f rb.tStorage) =
  (g rb.tStorage = f rb.tStorage)
Proof
  rw[rollback_state_component_equality]
QED

Definition MCopy_write_def:
  MCopy_write em offset sourceOffset sz =
  buffer_write offset (buffer_take sourceOffset sz em) em
End

val return_destination_tyinfo = Option.valOf $
  TypeBase.read {Thy="vfmContext", Tyop="return_destination"}

Theorem return_destination_case_rator[local] =
  DatatypeSimps.mk_case_rator_thm_tyinfo return_destination_tyinfo

Theorem return_destination_case_elim[local] =
  DatatypeSimps.mk_case_elim_thm_tyinfo return_destination_tyinfo

val start_tac =
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ simp [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ Cases_on ‘b’ \\ fs []
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR (FST r)` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]

val end_tac =
  irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ qmatch_goalsub_rename_tac ‘p = (_,_)’
  \\ Cases_on ‘p’ \\ gvs[]

val binop_tac =
  start_tac
  \\ gvs [step_inst_def,step_binop_def,step_modop_def,pop_stack_def,bind_def,
          ignore_bind_def,get_current_context_def,return_def,assert_def,
          set_current_context_def,consume_gas_def,push_stack_def,
          inc_pc_or_jump_def,is_call_def,with_zero_mod_def,step_monop_def,
          step_pop_def,step_exp_def,exp_cost_def,exponent_byte_size_def,
          step_msgParams_def,step_txParams_def,step_context_def,
          step_balance_def,access_address_split,HD_TAKE,Balance_gas_def,
          access_slot_split,step_sload_def,step_jump_def,set_jump_dest_def,
          step_jumpi_def,ExtCodeSize_gas_def,step_ext_code_size_def,
          step_log_def,push_logs_def,
          get_code_def,step_sstore_def,step_push_def,step_dup_def,
          step_swap_def,assert_not_static_def,get_static_def,
          step_sstore_gas_consumption_def
            |> SRULE [GSYM sstore_refund_updates_def,
                      GSYM sstore_base_gas_def],
          update_gas_refund_def
            |> oneline |> SRULE[pair_CASE_def],
          SStore_gas_def, UNCURRY, LAST_CONS_cond,
          GSYM sstore_write_accounts_updater_def, SStore_write_def,
          rollback_with_tStorage_simp,MCopy_gas_def,
          write_storage_def,update_accounts_def,write_transient_storage_def,
          get_tStorage_def,set_tStorage_def,get_gas_left_def,get_original_def,
          get_accounts_def,get_tx_params_def,step_call_data_load_def,
          get_call_data_def,memory_expansion_info_def,
          get_current_code_def,step_ext_code_copy_def,
          expand_memory_def,read_memory_def,Keccak256_gas_def,
          memory_cost_def,EL_TAKE,expanded_memory_def,step_mstore_def,
          CallDataCopy_gas_def,CodeCopy_gas_def,ExtCodeCopy_gas_def,
          ReturnDataCopy_gas_def,step_return_data_copy_def,
          get_return_data_check_def,get_return_data_def,NULL_EQ,
          Q.ISPEC`SND`COND_RAND,
          ExtCodeHash_gas_def,step_ext_code_hash_def,step_mload_def,
          step_copy_to_memory_def,copy_to_memory_def,step_blob_hash_def,
          write_memory_def,memory_expand_by_def,step_keccak256_def,
          step_block_hash_def,step_self_balance_def,get_callee_def]
  \\ Cases_on ‘FST r’ \\ gvs[]
  \\ TRY(Cases_on ‘(FST (HD (SND r).contexts)).stack’ >- gvs[] \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`HD (TAKE _ hs)` \\ Cases_on`hs` \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`DROP _ (hs:bytes32 list)` \\ Cases_on`hs` \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`HD (TAKE _ hs)` \\ Cases_on`hs` \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`_.txParams.prevHashes`
         \\ conj_tac >- (rw[] \\ gvs[]))
  \\ TRY(qmatch_asmsub_rename_tac`COND (b = 0w) NONE` \\
         Cases_on`b = 0w` \\
         gvs[set_current_context_def,return_def,bind_def,
             assert_def])
  \\ TRY(qmatch_assum_abbrev_tac`(ad,sd) = sstore_refund_updates x y z`
         \\ Cases_on`sstore_refund_updates x y z` \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`MCopy_write`
         \\ conj_tac >- simp[MCopy_write_def])
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {_}’ $ rewrite_tac o single o GSYM
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []))
  \\ end_tac

Theorem SPEC_Stop_outermost:
  SPEC EVM_MODEL
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
     cond (NULL cs ∧ ISL e))
    {(pc,Stop)}
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_ReturnData [] * evm_Exception (INR NONE) *
     evm_Rollback (case p.outputTo of Memory _ => rb | Code addr =>
                   rb with accounts updated_by (λaccounts.
                      update_account addr
                        (lookup_account addr accounts with code := [])
                        accounts)))
Proof
  start_tac
  \\ gvs [step_inst_def,bind_def,ignore_bind_def,set_return_data_def,
          get_current_context_def,return_def,set_current_context_def,
          finish_def,handle_step_def,handle_def,handle_create_def,
          get_return_data_def,get_output_to_def,handle_exception_def,
          reraise_def,get_num_contexts_def,NULL_EQ,assert_def,
          return_destination_case_rator,consume_gas_def,update_accounts_def,
          CaseEq"return_destination",CaseEq"prod",CaseEq"sum"]
  \\ end_tac
QED

Theorem SPEC_Stop_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc Stop * evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         calleeGasLeft = p.gasLimit - g ∧
         calleeGasLeft ≤ caller.gasUsed))
  {}
  (evm_Stack ((case p.outputTo of Code addr => w2w addr
                                        | _ => 1w)::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback (case p.outputTo of Memory _ => rb | Code addr =>
                 rb with accounts updated_by (λaccounts.
                    update_account addr
                      (lookup_account addr accounts with code := [])
                      accounts)) *
   evm_GasUsed (caller.gasUsed - calleeGasLeft) *
   evm_JumpDest caller.jumpDest *
   evm_Logs (caller.logs ++ l) *
   evm_AddRefund (caller.addRefund + ar) *
   evm_SubRefund (caller.subRefund + sr))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_EMPTY,
                  EMPTY_evm2set,STAR_evm_hide_Parsed, STAR_CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ qmatch_asmsub_abbrev_tac`_ < stack_limit ∧ is_ret ∧ _`
  \\ last_x_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ `¬(SUC (LENGTH (TL (SND r).contexts)) ≤ 1)` by (
       Cases_on`TL (SND r).contexts` \\ gvs[])
  \\ gvs[step_inst_def,bind_def,ignore_bind_def,set_return_data_def,
         get_current_context_def,return_def,set_current_context_def,
         finish_def,handle_step_def,handle_def,handle_create_def,
         get_return_data_def,get_output_to_def,assert_def,reraise_def,
         return_destination_case_rator,consume_gas_def,update_accounts_def]
  \\ qmatch_assum_rename_tac`wf_state r2`
  \\ `(FST (HD r2.contexts)).msgParams.parsed =
      parse_code 0 FEMPTY (FST (HD r2.contexts)).msgParams.code`
     by (gvs[wf_state_def] \\ Cases_on`r2.contexts` \\ gvs[wf_context_def])
  \\ `¬(SUC (LENGTH cs) ≤ 1)` by (Cases_on`cs` \\ gvs[])
  \\ gvs[CaseEq"prod",CaseEq"sum",CaseEq"return_destination",
         handle_exception_def,get_num_contexts_def,inc_pc_def,
         pop_and_incorporate_context_def,push_stack_def,
         bind_def,ignore_bind_def,return_def,get_current_context_def,
         set_current_context_def,assert_def,get_return_data_def,
         get_output_to_def,set_return_data_def,Abbr`calleeGasLeft`,
         write_memory_def,pop_context_def,unuse_gas_def,push_logs_def,
         update_gas_refund_def,get_gas_left_def]
  \\ (rpt (conj_tac >- (
        gvs[Abbr`all_pcs`,TO_FLOOKUP,SUBSET_DEF, PULL_EXISTS] \\
        TRY (rpt strip_tac \\ drule FLOOKUP_parse_code_SOME_less_LENGTH
             \\ simp[] \\ NO_TAC)
        \\ metis_tac[NOT_SOME_NONE])))
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {}’ mp_tac
        \\ simp[EXTENSION,Abbr`all_pcs`] \\ rw [EQ_IMP_THM]
        \\ gvs[SUBSET_DEF,PULL_EXISTS]
        \\ last_x_assum(qspec_then`x`mp_tac)
        \\ simp[]
        \\ strip_tac \\ gvs[FORALL_PROD, TO_FLOOKUP]
        \\ metis_tac[option_CASES]))
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ ntac 2 strip_tac
  \\ gvs[SUBSET_DEF, PULL_EXISTS, TO_FLOOKUP, Abbr`all_pcs`]
  \\ qmatch_assum_rename_tac`HasParsed pc2 ∉ dom`
  \\ first_x_assum(qspec_then`pc2`mp_tac)
  \\ simp[]
  \\ strip_tac \\ gvs[]
QED

(* ----------------------------------------------------------------------------- *)
(* Exceptional halts                                                             *)
(* ----------------------------------------------------------------------------- *)

(* An exception other than Revert consumes all of the context's remaining gas
   and clears the return data. In the outermost context execution then stops
   with the exception; in an inner context the callee is popped, its state
   changes are rolled back, and the caller resumes with 0 pushed.

   The rules below that hold for a family of instructions take the shape of
   the instruction's semantics as a hypothesis, e.g. that it starts by popping
   n arguments. Each is discharged for a concrete instruction by unfolding
   step_inst_def and its step_* definition. *)

fun exn_outer_tac ths =
  start_tac
  \\ gvs (ths @ [pop_stack_def,fail_def,bind_def,ignore_bind_def,
          handle_step_def,vfm_abort_def,handle_def,handle_create_def,
          get_return_data_def,get_output_to_def,reraise_def,
          handle_exception_def,get_gas_left_def,consume_gas_def,
          set_return_data_def,get_current_context_def,return_def,
          set_current_context_def,get_num_contexts_def,NULL_EQ,assert_def,
          return_destination_case_elim])
  \\ end_tac

fun exn_inner_tac ths =
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_EMPTY,
                  EMPTY_evm2set,STAR_evm_hide_Parsed, STAR_CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ qmatch_asmsub_abbrev_tac`_ < stack_limit ∧ is_ret ∧ _`
  \\ last_x_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ `¬(SUC (LENGTH (TL (SND r).contexts)) ≤ 1)` by (
       Cases_on`TL (SND r).contexts` \\ gvs[])
  \\ rpt (qpat_x_assum`SOME _ = _`(assume_tac o SYM))
  \\ rpt (qpat_x_assum`_ = step_inst _`(assume_tac o SYM))
  \\ gvs (ths @ [pop_stack_def,fail_def,bind_def,ignore_bind_def,
         handle_step_def,vfm_abort_def,handle_def,handle_create_def,
         get_return_data_def,get_output_to_def,reraise_def,
         get_current_context_def,return_def,set_current_context_def,
         assert_def,consume_gas_def,return_destination_case_rator])
  \\ qmatch_assum_rename_tac`wf_state r2`
  \\ `(FST (HD r2.contexts)).msgParams.parsed =
      parse_code 0 FEMPTY (FST (HD r2.contexts)).msgParams.code`
     by (gvs[wf_state_def] \\ Cases_on`r2.contexts` \\ gvs[wf_context_def])
  \\ `¬(SUC (LENGTH cs) ≤ 1)` by (Cases_on`cs` \\ gvs[])
  \\ Cases_on`p.outputTo`
  \\ gvs[CaseEq"prod",CaseEq"sum",handle_exception_def,get_num_contexts_def,
         inc_pc_def,pop_and_incorporate_context_def,push_stack_def,
         bind_def,ignore_bind_def,return_def,get_current_context_def,
         set_current_context_def,assert_def,get_return_data_def,
         get_output_to_def,set_return_data_def,get_gas_left_def,
         consume_gas_def,write_memory_def,pop_context_def,unuse_gas_def,
         set_rollback_def]
  \\ (rpt (conj_tac >- (
        gvs[Abbr`all_pcs`,TO_FLOOKUP,SUBSET_DEF, PULL_EXISTS] \\
        TRY (rpt strip_tac \\ drule FLOOKUP_parse_code_SOME_less_LENGTH
             \\ simp[] \\ NO_TAC)
        \\ metis_tac[NOT_SOME_NONE])))
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {}’ mp_tac
        \\ simp[EXTENSION,Abbr`all_pcs`] \\ rw [EQ_IMP_THM]
        \\ gvs[SUBSET_DEF,PULL_EXISTS]
        \\ last_x_assum(qspec_then`x`mp_tac)
        \\ simp[]
        \\ strip_tac \\ gvs[FORALL_PROD, TO_FLOOKUP]
        \\ metis_tac[option_CASES]))
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ ntac 2 strip_tac
  \\ gvs[SUBSET_DEF, PULL_EXISTS, TO_FLOOKUP, Abbr`all_pcs`]
  \\ qmatch_assum_rename_tac`HasParsed pc2 ∉ dom`
  \\ first_x_assum(qspec_then`pc2`mp_tac)
  \\ simp[]
  \\ strip_tac \\ gvs[]

Theorem SPEC_StackUnderflow_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ LENGTH ss < n ∧
           ∃k. step_inst inst = bind (pop_stack n) k))
    {(pc,inst)}
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME StackUnderflow)))
Proof
  exn_outer_tac []
QED

Theorem SPEC_OutOfGas_pop_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ n ≤ LENGTH ss ∧
           p.gasLimit < g + cost (TAKE n ss) ∧
           ∃k. step_inst inst =
               bind (pop_stack n)
                 (λargs. ignore_bind (consume_gas (cost args)) (k args))))
    {(pc,inst)}
    (evm_Stack (DROP n ss) * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME OutOfGas)))
Proof
  exn_outer_tac []
QED

Theorem SPEC_OutOfGas_outermost:
  SPEC EVM_MODEL
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ p.gasLimit < g + c ∧
           ∃k. step_inst inst = ignore_bind (consume_gas c) k))
    {(pc,inst)}
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME OutOfGas)))
Proof
  exn_outer_tac []
QED

Theorem SPEC_StackOverflow_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ LENGTH ss = stack_limit ∧
           g + c ≤ p.gasLimit ∧
           ∃k. step_inst inst = ignore_bind (consume_gas c) k ∧
               ∀s. s.contexts ≠ [] ∧
                   LENGTH (FST (HD s.contexts)).stack = stack_limit ⇒
                   k s = (INR (SOME StackOverflow), s)))
    {(pc,inst)}
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME StackOverflow)))
Proof
  exn_outer_tac []
QED

Theorem SPEC_StackUnderflow_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc inst *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         LENGTH ss < n ∧
         ∃k. step_inst inst = bind (pop_stack n) k))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac []
QED

Theorem SPEC_OutOfGas_pop_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc inst *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         n ≤ LENGTH ss ∧ p.gasLimit < g + cost (TAKE n ss) ∧
         ∃k. step_inst inst =
             bind (pop_stack n)
               (λargs. ignore_bind (consume_gas (cost args)) (k args))))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac []
QED

Theorem SPEC_OutOfGas_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc inst *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         p.gasLimit < g + c ∧
         ∃k. step_inst inst = ignore_bind (consume_gas c) k))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac []
QED

Theorem SPEC_StackOverflow_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc inst *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         LENGTH ss = stack_limit ∧ g + c ≤ p.gasLimit ∧
         ∃k. step_inst inst = ignore_bind (consume_gas c) k ∧
             ∀s. s.contexts ≠ [] ∧
                 LENGTH (FST (HD s.contexts)).stack = stack_limit ⇒
                 k s = (INR (SOME StackOverflow), s)))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac []
QED

Triviality one_le_LENGTH:
  1 ≤ LENGTH l ⇔ l ≠ []
Proof
  Cases_on`l` \\ simp[]
QED

Theorem SPEC_InvalidJumpDest_Jump_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_JumpDest j * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ ss ≠ [] ∧
           g + static_gas Jump ≤ p.gasLimit ∧
           ¬(w2n (HD ss) < LENGTH p.code ∧
             FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest)))
    {(pc,Jump)}
    (evm_Stack (TL ss) * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_JumpDest (SOME (w2n (HD ss))) *
     evm_Exception (INR (SOME InvalidJumpDest)))
Proof
  exn_outer_tac [step_inst_def,step_jump_def,set_jump_dest_def,inc_pc_or_jump_def,
                 is_call_def,EL_TAKE,HD_TAKE,GSYM rich_listTheory.TAIL_BY_DROP,
                 NOT_NIL_EQ_LENGTH_NOT_0,SF CONJ_ss]
QED

Theorem SPEC_InvalidJumpDest_JumpI_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_JumpDest j * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ 2 ≤ LENGTH ss ∧ EL 1 ss ≠ 0w ∧
           g + static_gas JumpI ≤ p.gasLimit ∧
           ¬(w2n (HD ss) < LENGTH p.code ∧
             FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest)))
    {(pc,JumpI)}
    (evm_Stack (DROP 2 ss) * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_JumpDest (SOME (w2n (HD ss))) *
     evm_Exception (INR (SOME InvalidJumpDest)))
Proof
  exn_outer_tac [step_inst_def,step_jumpi_def,set_jump_dest_def,inc_pc_or_jump_def,
                 is_call_def,EL_TAKE,HD_TAKE,GSYM rich_listTheory.TAIL_BY_DROP,
                 NOT_NIL_EQ_LENGTH_NOT_0,SF CONJ_ss]
QED

Theorem SPEC_OutOfBoundsRead_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Memory m * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ 3 ≤ LENGTH ss ∧
           offset = w2n (EL 0 ss) ∧ sz = w2n (EL 2 ss) ∧
           sourceOffset = w2n (EL 1 ss) ∧
           LENGTH rd < sourceOffset + sz ∧
           g + ReturnDataCopy_gas m offset sz ≤ p.gasLimit))
    {(pc,ReturnDataCopy)}
    (evm_Stack (DROP 3 ss) * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] * evm_Memory m *
     evm_Exception (INR (SOME OutOfBoundsRead)))
Proof
  exn_outer_tac [step_inst_def,step_return_data_copy_def,copy_to_memory_def,
                 memory_expansion_info_def,get_return_data_check_def,
                 ReturnDataCopy_gas_def,memory_cost_def,EL_TAKE,HD_TAKE]
QED

Theorem SPEC_InvalidJumpDest_Jump_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc Jump *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         ss ≠ [] ∧ g + static_gas Jump ≤ p.gasLimit ∧
         ¬(w2n (HD ss) < LENGTH p.code ∧
           FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest)))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac [step_inst_def,step_jump_def,set_jump_dest_def,inc_pc_or_jump_def,
                 is_call_def,EL_TAKE,HD_TAKE,GSYM rich_listTheory.TAIL_BY_DROP,
                 one_le_LENGTH,SF CONJ_ss]
QED

Theorem SPEC_InvalidJumpDest_JumpI_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc JumpI *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         2 ≤ LENGTH ss ∧ EL 1 ss ≠ 0w ∧
         g + static_gas JumpI ≤ p.gasLimit ∧
         ¬(w2n (HD ss) < LENGTH p.code ∧
           FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest)))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac [step_inst_def,step_jumpi_def,set_jump_dest_def,inc_pc_or_jump_def,
                 is_call_def,EL_TAKE,HD_TAKE,GSYM rich_listTheory.TAIL_BY_DROP,
                 SF CONJ_ss]
QED

Theorem SPEC_OutOfBoundsRead_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc ReturnDataCopy *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         3 ≤ LENGTH ss ∧
         offset = w2n (EL 0 ss) ∧ sz = w2n (EL 2 ss) ∧
         sourceOffset = w2n (EL 1 ss) ∧
         LENGTH rd < sourceOffset + sz ∧
         g + ReturnDataCopy_gas m offset sz ≤ p.gasLimit))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac [step_inst_def,step_return_data_copy_def,copy_to_memory_def,
                 memory_expansion_info_def,get_return_data_check_def,
                 ReturnDataCopy_gas_def,memory_cost_def,EL_TAKE,HD_TAKE]
QED

Theorem SPEC_WriteInStaticContext_TStore_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ 2 ≤ LENGTH ss ∧ p.static ∧
           g + warm_access_cost ≤ p.gasLimit))
    {(pc,TStore)}
    (evm_Stack (DROP 2 ss) * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME WriteInStaticContext)))
Proof
  exn_outer_tac [step_inst_def,step_sstore_def,assert_not_static_def,
                 get_static_def,get_callee_def]
QED

Theorem SPEC_WriteInStaticContext_Log_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Memory m * evm_Exception e *
     cond (NULL cs ∧ ISL e ∧ 2 + n ≤ LENGTH ss ∧ p.static ∧
           offset = w2n (EL 0 ss) ∧ sz = w2n (EL 1 ss) ∧
           dynamicGas = log_topic_cost * n + log_data_cost * sz +
                        memory_cost m offset sz ∧
           g + static_gas (Log n) + dynamicGas ≤ p.gasLimit))
    {(pc,Log n)}
    (evm_Stack (DROP (2 + n) ss) * evm_PC pc * evm_MsgParams p *
     evm_Contexts cs * evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Memory (expanded_memory m offset sz) *
     evm_Exception (INR (SOME WriteInStaticContext)))
Proof
  exn_outer_tac [step_inst_def,step_log_def,memory_expansion_info_def,
                 expand_memory_def,memory_cost_def,expanded_memory_def,
                 memory_expand_by_def,EL_TAKE,HD_TAKE,assert_not_static_def,
                 get_static_def,get_callee_def]
QED

Theorem SPEC_WriteInStaticContext_SelfDestruct_outermost:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     evm_Rollback rb * evm_Msdomain d *
     cond (NULL cs ∧ ISL e ∧ ss ≠ [] ∧ p.static ∧
           addr = w2w (HD ss) ∧ access_check d addr ∧
           sender = lookup_account p.callee rb.accounts ∧
           transferCost = (if 0 < sender.balance ∧
                              account_empty (lookup_account addr rb.accounts)
                           then self_destruct_new_account_cost else 0) ∧
           g + static_gas SelfDestruct + zero_warm (access_cost rb addr) +
           transferCost ≤ p.gasLimit))
    {(pc,SelfDestruct)}
    (evm_Stack (TL ss) * evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME WriteInStaticContext)) *
     evm_Rollback (accesses_add addr rb) * evm_Msdomain (msdomain_add addr d))
Proof
  exn_outer_tac [step_inst_def,step_self_destruct_def,access_address_split,
                 set_return_data_def,get_accounts_def,HD_TAKE,one_le_LENGTH,
                 assert_not_static_def,get_static_def,get_callee_def,
                 GSYM rich_listTheory.TAIL_BY_DROP,SUB_ADD]
QED

Theorem SPEC_WriteInStaticContext_TStore_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc TStore *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         2 ≤ LENGTH ss ∧ p.static ∧
         g + warm_access_cost ≤ p.gasLimit))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac [step_inst_def,step_sstore_def,assert_not_static_def,get_static_def,get_callee_def]
QED

Theorem SPEC_WriteInStaticContext_Log_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc (Log n) *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         2 + n ≤ LENGTH ss ∧ p.static ∧
         offset = w2n (EL 0 ss) ∧ sz = w2n (EL 1 ss) ∧
         dynamicGas = log_topic_cost * n + log_data_cost * sz +
                      memory_cost m offset sz ∧
         g + static_gas (Log n) + dynamicGas ≤ p.gasLimit))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac [step_inst_def,step_log_def,memory_expansion_info_def,
                 expand_memory_def,memory_cost_def,EL_TAKE,HD_TAKE,
                 assert_not_static_def,get_static_def,get_callee_def,
                 Abbr`dynamicGas`]
QED

Theorem SPEC_WriteInStaticContext_SelfDestruct_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Msdomain d *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc SelfDestruct *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         ss ≠ [] ∧ p.static ∧
         addr = w2w (HD ss) ∧ access_check d addr ∧
         sender = lookup_account p.callee rb.accounts ∧
         transferCost = (if 0 < sender.balance ∧
                            account_empty (lookup_account addr rb.accounts)
                         then self_destruct_new_account_cost else 0) ∧
         g + static_gas SelfDestruct + zero_warm (access_cost rb addr) +
         transferCost ≤ p.gasLimit))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Msdomain (msdomain_add addr d) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  exn_inner_tac [step_inst_def,step_self_destruct_def,access_address_split,
                 set_return_data_def,get_accounts_def,HD_TAKE,one_le_LENGTH,
                 assert_not_static_def,get_static_def,get_callee_def]
QED

(* Non-vacuity witnesses: concrete opcodes meet the shape hypotheses of the
   generic exceptional-halt rules above. *)

Theorem witness_StackUnderflow_Add:
  ∃k. step_inst Add = bind (pop_stack 2) k
Proof
  simp[step_inst_def,step_binop_def]
  \\ irule_at Any EQ_REFL
QED

Theorem witness_OutOfGas_pop_Add:
  ∃k. step_inst Add =
      bind (pop_stack 2)
        (λargs. ignore_bind (consume_gas (K (static_gas Add) args)) (k args))
Proof
  simp[step_inst_def,step_binop_def]
  \\ qexists_tac`λargs. push_stack (word_add (EL 0 args) (EL 1 args))`
  \\ simp[]
QED

Theorem witness_OutOfGas_Push:
  ∃k. step_inst (Push n ws) = ignore_bind (consume_gas (static_gas (Push n ws))) k
Proof
  simp[step_inst_def,step_push_def]
  \\ irule_at Any EQ_REFL
QED

Theorem witness_StackOverflow_Push:
  ∃k. step_inst (Push n ws) =
      ignore_bind (consume_gas (static_gas (Push n ws))) k ∧
      ∀s. s.contexts ≠ [] ∧
          LENGTH (FST (HD s.contexts)).stack = stack_limit ⇒
          k s = (INR (SOME StackOverflow), s)
Proof
  qexists_tac`push_stack (word_of_bytes F 0w (REVERSE ws))`
  \\ rw[step_inst_def,step_push_def,push_stack_def,bind_def,ignore_bind_def,
        get_current_context_def,return_def,assert_def]
QED

Theorem SPEC_Add:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Add ≤ p.gasLimit))
    {(pc,Add)}
    (evm_Stack (word_add (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Add)) *
     evm_GasUsed (g + static_gas Add) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Mul:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Mul ≤ p.gasLimit))
    {(pc,Mul)}
    (evm_Stack (word_mul (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Mul)) *
     evm_GasUsed (g + static_gas Mul) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Sub:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Sub ≤ p.gasLimit))
    {(pc,Sub)}
    (evm_Stack (word_sub (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Sub)) *
     evm_GasUsed (g + static_gas Sub) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Div:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Div ≤ p.gasLimit))
    {(pc,Div)}
    (evm_Stack (with_zero word_div (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Div)) *
     evm_GasUsed (g + static_gas Div) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SDiv:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas SDiv ≤ p.gasLimit))
    {(pc,SDiv)}
    (evm_Stack (with_zero word_quot (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode SDiv)) *
     evm_GasUsed (g + static_gas SDiv) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Mod:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Mod ≤ p.gasLimit))
    {(pc,Mod)}
    (evm_Stack (with_zero word_mod (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Mod)) *
     evm_GasUsed (g + static_gas Mod) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SMod:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas SMod ≤ p.gasLimit))
    {(pc,SMod)}
    (evm_Stack (with_zero word_rem (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode SMod)) *
     evm_GasUsed (g + static_gas SMod) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_AddMod:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (3 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas AddMod ≤ p.gasLimit))
    {(pc,AddMod)}
    (evm_Stack (with_zero_mod (+) (EL 0 ss) (EL 1 ss) (EL 2 ss) :: DROP 3 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode AddMod)) *
     evm_GasUsed (g + static_gas AddMod) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_MulMod:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (3 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas MulMod ≤ p.gasLimit))
    {(pc,MulMod)}
    (evm_Stack (with_zero_mod $* (EL 0 ss) (EL 1 ss) (EL 2 ss) :: DROP 3 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode MulMod)) *
     evm_GasUsed (g + static_gas MulMod) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Exp:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧
         ISL e ∧ g + exp_cost (EL 1 ss) ≤ p.gasLimit))
  {(pc,Exp)}
  (evm_Stack ((EL 0 ss) ** (EL 1 ss) :: DROP 2 ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode Exp)) *
   evm_GasUsed (g + exp_cost (EL 1 ss)) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SignExtend:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas SignExtend ≤ p.gasLimit))
    {(pc,SignExtend)}
    (evm_Stack (sign_extend (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode SignExtend)) *
     evm_GasUsed (g + static_gas SignExtend) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_LT:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas LT ≤ p.gasLimit))
    {(pc,LT)}
    (evm_Stack (b2w ((w2n $ EL 0 ss) < (w2n $ EL 1 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode LT)) *
     evm_GasUsed (g + static_gas LT) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_GT:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas GT ≤ p.gasLimit))
    {(pc,GT)}
    (evm_Stack (b2w ((w2n $ EL 0 ss) > (w2n $ EL 1 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode GT)) *
     evm_GasUsed (g + static_gas GT) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SLT:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas SLT ≤ p.gasLimit))
    {(pc,SLT)}
    (evm_Stack (b2w ((EL 0 ss) < (EL 1 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode SLT)) *
     evm_GasUsed (g + static_gas SLT) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SGT:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas SGT ≤ p.gasLimit))
    {(pc,SGT)}
    (evm_Stack (b2w ((EL 0 ss) > (EL 1 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode SGT)) *
     evm_GasUsed (g + static_gas SGT) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Eq:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Eq ≤ p.gasLimit))
    {(pc,Eq)}
    (evm_Stack (b2w ((EL 0 ss) = (EL 1 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Eq)) *
     evm_GasUsed (g + static_gas Eq) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_IsZero:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (ss ≠ [] ∧ j = NONE ∧
           ISL e ∧ g + static_gas IsZero ≤ p.gasLimit))
    {(pc,IsZero)}
    (evm_Stack (b2w (EL 0 ss = 0w) :: TL ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode IsZero)) *
     evm_GasUsed (g + static_gas IsZero) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_And:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas And ≤ p.gasLimit))
    {(pc,And)}
    (evm_Stack (word_and (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode And)) *
     evm_GasUsed (g + static_gas And) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Or:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Or ≤ p.gasLimit))
    {(pc,Or)}
    (evm_Stack (word_or (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Or)) *
     evm_GasUsed (g + static_gas Or) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_XOr:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas XOr ≤ p.gasLimit))
    {(pc,XOr)}
    (evm_Stack (word_xor (EL 0 ss) (EL 1 ss) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode XOr)) *
     evm_GasUsed (g + static_gas XOr) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Not:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (ss ≠ [] ∧ j = NONE ∧
           ISL e ∧ g + static_gas Not ≤ p.gasLimit))
    {(pc,Not)}
    (evm_Stack (¬(HD ss) :: TL ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Not)) *
     evm_GasUsed (g + static_gas Not) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Byte:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas Byte ≤ p.gasLimit))
    {(pc,Byte)}
    (evm_Stack ((if w2n (EL 0 ss) < 32
                 then w2w (get_byte (EL 0 ss) (EL 1 ss) T)
                 else 0w)
                :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Byte)) *
     evm_GasUsed (g + static_gas Byte) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ShL:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas ShL ≤ p.gasLimit))
    {(pc,ShL)}
    (evm_Stack ((EL 1 ss << w2n (EL 0 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode ShL)) *
     evm_GasUsed (g + static_gas ShL) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ShR:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas ShR ≤ p.gasLimit))
    {(pc,ShR)}
    (evm_Stack ((EL 1 ss >>> w2n (EL 0 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode ShR)) *
     evm_GasUsed (g + static_gas ShR) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SAR:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (2 ≤ LENGTH ss ∧ j = NONE ∧
           ISL e ∧ g + static_gas SAR ≤ p.gasLimit))
    {(pc,SAR)}
    (evm_Stack ((EL 1 ss >> w2n (EL 0 ss)) :: DROP 2 ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode SAR)) *
     evm_GasUsed (g + static_gas SAR) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CLZ:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (ss ≠ [] ∧ j = NONE ∧
           ISL e ∧ g + static_gas CLZ ≤ p.gasLimit))
    {(pc,CLZ)}
    (evm_Stack (n2w (if HD ss = 0w then 256
                     else 255 - LOG2 (w2n (HD ss))) :: TL ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode CLZ)) *
     evm_GasUsed (g + static_gas CLZ) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Keccak256:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         sz = w2n (EL 1 ss) ∧ offset = w2n (EL 0 ss) ∧
         g + Keccak256_gas m offset sz ≤ p.gasLimit ∧
         em = expanded_memory m offset sz))
  {(pc,Keccak256)}
  (evm_Stack (word_of_bytes T 0w (Keccak_256_w64 $
               buffer_take offset sz em) :: DROP 2 ss) *
   evm_JumpDest j * evm_Exception e * evm_Memory em *
   evm_PC (pc + LENGTH (opcode Keccak256)) *
   evm_GasUsed (g + Keccak256_gas m offset sz) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Address:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas Address ≤ p.gasLimit))
  {(pc,Address)}
  (evm_Stack (w2w (p.callee) :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode Address)) *
   evm_GasUsed (g + static_gas Address) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Balance:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb * evm_Msdomain d *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         a = (w2w (EL 0 ss)) ∧ access_check d a ∧
         g + Balance_gas rb a ≤ p.gasLimit))
  {(pc,Balance)}
  (evm_Stack (n2w (lookup_account a rb.accounts).balance :: TL ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode Balance)) *
   evm_Rollback (accesses_add a rb) *
   evm_Msdomain (msdomain_add a d) *
   evm_GasUsed (g + Balance_gas rb a) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Origin:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_TxParams t * evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas Origin ≤ p.gasLimit))
  {(pc,Origin)}
  (evm_Stack (w2w (t.origin) :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode Origin)) *
   evm_GasUsed (g + static_gas Origin) *
   evm_MsgParams p * evm_TxParams t)
Proof binop_tac
QED

Theorem SPEC_Caller:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas Caller ≤ p.gasLimit))
  {(pc,Caller)}
  (evm_Stack (w2w (p.caller) :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode Caller)) *
   evm_GasUsed (g + static_gas Caller) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CallValue:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas CallValue ≤ p.gasLimit))
  {(pc,CallValue)}
  (evm_Stack (n2w (p.value) :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode CallValue)) *
   evm_GasUsed (g + static_gas CallValue) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CallDataLoad:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         g + static_gas CallDataLoad ≤ p.gasLimit))
  {(pc,CallDataLoad)}
  (evm_Stack (word_of_bytes F 0w (REVERSE $ take_pad_0 32 $
              DROP (w2n (HD ss)) (buffer_to_list p.data)) :: TL ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode CallDataLoad)) *
   evm_GasUsed (g + static_gas CallDataLoad) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CallDataSize:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas CallDataSize ≤ p.gasLimit))
  {(pc,CallDataSize)}
  (evm_Stack (n2w (buffer_length p.data) :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode CallDataSize)) *
   evm_GasUsed (g + static_gas CallDataSize) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CallDataCopy:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (3 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧ sz = w2n (EL 2 ss) ∧
         g + CallDataCopy_gas m offset sz ≤ p.gasLimit ∧
         em = expanded_memory m offset sz))
  {(pc,CallDataCopy)}
  (evm_Stack (DROP 3 ss) *
   evm_JumpDest j * evm_Exception e *
   evm_Memory (buffer_write offset
                 (take_pad_0 sz (DROP (w2n (EL 1 ss)) (buffer_to_list p.data)))
                 em) *
   evm_PC (pc + LENGTH (opcode CallDataCopy)) *
   evm_GasUsed (g + CallDataCopy_gas m offset sz) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CodeSize:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas CodeSize ≤ p.gasLimit))
  {(pc,CodeSize)}
  (evm_Stack (n2w (LENGTH p.code) :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode CodeSize)) *
   evm_GasUsed (g + static_gas CodeSize) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CodeCopy:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (3 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧ sz = w2n (EL 2 ss) ∧
         g + CodeCopy_gas m offset sz ≤ p.gasLimit ∧
         em = expanded_memory m offset sz))
  {(pc,CodeCopy)}
  (evm_Stack (DROP 3 ss) *
   evm_JumpDest j * evm_Exception e *
   evm_Memory (buffer_write offset
                 (take_pad_0 sz (DROP (w2n (EL 1 ss)) p.code)) em) *
   evm_PC (pc + LENGTH (opcode CodeCopy)) *
   evm_GasUsed (g + CodeCopy_gas m offset sz) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_GasPrice:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas GasPrice ≤ p.gasLimit))
  {(pc,GasPrice)}
  (evm_Stack (n2w (t.gasPrice) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode GasPrice)) *
   evm_GasUsed (g + static_gas GasPrice) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ExtCodeSize:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb * evm_Msdomain d *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         a = w2w (EL 0 ss) ∧ access_check d a ∧
         g + ExtCodeSize_gas rb a ≤ p.gasLimit))
  {(pc,ExtCodeSize)}
  (evm_Stack (n2w (LENGTH (lookup_account a rb.accounts).code) :: TL ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode ExtCodeSize)) *
   evm_Rollback (accesses_add a rb) *
   evm_Msdomain (msdomain_add a d) *
   evm_GasUsed (g + ExtCodeSize_gas rb a) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ExtCodeCopy:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m * evm_Rollback rb * evm_Msdomain d *
   cond (4 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         a = w2w (EL 0 ss) ∧ access_check d a ∧
         offset = w2n (EL 1 ss) ∧ sz = w2n (EL 3 ss) ∧
         g + ExtCodeCopy_gas m rb a offset sz ≤ p.gasLimit ∧
         em = expanded_memory m offset sz))
  {(pc,ExtCodeCopy)}
  (evm_Stack (DROP 4 ss) *
   evm_JumpDest j * evm_Exception e *
   evm_Memory (buffer_write offset (take_pad_0 sz (DROP (w2n (EL 2 ss))
                 (lookup_account a rb.accounts).code)) em) *
   evm_PC (pc + LENGTH (opcode ExtCodeCopy)) *
   evm_Rollback (accesses_add a rb) *
   evm_Msdomain (msdomain_add a d) *
   evm_GasUsed (g + ExtCodeCopy_gas m rb a offset sz) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ReturnDataSize:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_ReturnData rd *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas ReturnDataSize ≤ p.gasLimit))
  {(pc,ReturnDataSize)}
  (evm_Stack (n2w (LENGTH rd) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_ReturnData rd *
   evm_PC (pc + LENGTH (opcode ReturnDataSize)) *
   evm_GasUsed (g + static_gas ReturnDataSize) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ReturnDataCopy:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_ReturnData rd * evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (3 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧ sz = w2n (EL 2 ss) ∧
         sourceOffset = w2n (EL 1 ss) ∧
         sourceOffset + sz ≤ LENGTH rd ∧
         g + ReturnDataCopy_gas m offset sz ≤ p.gasLimit ∧
         em = expanded_memory m offset sz))
  {(pc,ReturnDataCopy)}
  (evm_Stack (DROP 3 ss) *
   evm_ReturnData rd * evm_JumpDest j * evm_Exception e *
   evm_Memory (buffer_write offset (take_pad_0 sz (DROP sourceOffset rd)) em) *
   evm_PC (pc + LENGTH (opcode ReturnDataCopy)) *
   evm_GasUsed (g + ReturnDataCopy_gas m offset sz) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ExtCodeHash:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb * evm_Msdomain d *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         a = w2w (HD ss) ∧ access_check d a ∧
         account = lookup_account a rb.accounts ∧
         g + ExtCodeHash_gas rb a ≤ p.gasLimit))
  {(pc,ExtCodeHash)}
  (evm_Stack (
    (if account_empty account then 0w else
     word_of_bytes T 0w (Keccak_256_w64 account.code))
    :: TL ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode ExtCodeHash)) *
   evm_Rollback (accesses_add a rb) *
   evm_Msdomain (msdomain_add a d) *
   evm_GasUsed (g + ExtCodeHash_gas rb a) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_BlockHash:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         number = w2n (HD ss) ∧
         inRange = (number < t.blockNumber ∧ t.blockNumber - 256 ≤ number) ∧
         index = t.blockNumber - number - 1 ∧
         g + static_gas BlockHash ≤ p.gasLimit))
  {(pc,BlockHash)}
  (evm_Stack ((if inRange ∧ index < LENGTH t.prevHashes
               then EL index t.prevHashes else 0w) :: TL ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode BlockHash)) *
   evm_GasUsed (g + static_gas BlockHash) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_CoinBase:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas CoinBase ≤ p.gasLimit))
  {(pc,CoinBase)}
  (evm_Stack (w2w (t.blockCoinBase) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode CoinBase)) *
   evm_GasUsed (g + static_gas CoinBase) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_TimeStamp:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas TimeStamp ≤ p.gasLimit))
  {(pc,TimeStamp)}
  (evm_Stack (n2w (t.blockTimeStamp) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode TimeStamp)) *
   evm_GasUsed (g + static_gas TimeStamp) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Number:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas Number ≤ p.gasLimit))
  {(pc,Number)}
  (evm_Stack (n2w (t.blockNumber) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode Number)) *
   evm_GasUsed (g + static_gas Number) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_PrevRandao:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas PrevRandao ≤ p.gasLimit))
  {(pc,PrevRandao)}
  (evm_Stack (t.prevRandao :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode PrevRandao)) *
   evm_GasUsed (g + static_gas PrevRandao) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_GasLimit:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas GasLimit ≤ p.gasLimit))
  {(pc,GasLimit)}
  (evm_Stack (n2w (t.blockGasLimit) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode GasLimit)) *
   evm_GasUsed (g + static_gas GasLimit) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_ChainId:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas ChainId ≤ p.gasLimit))
  {(pc,ChainId)}
  (evm_Stack (n2w (t.chainId) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode ChainId)) *
   evm_GasUsed (g + static_gas ChainId) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SelfBalance:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas SelfBalance ≤ p.gasLimit))
  {(pc,SelfBalance)}
  (evm_Stack (n2w (lookup_account p.callee rb.accounts).balance :: ss) *
   evm_JumpDest j * evm_Exception e *
   evm_PC (pc + LENGTH (opcode SelfBalance)) *
   evm_Rollback rb *
   evm_GasUsed (g + static_gas SelfBalance) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_BaseFee:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas BaseFee ≤ p.gasLimit))
  {(pc,BaseFee)}
  (evm_Stack (n2w (t.baseFeePerGas) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode BaseFee)) *
   evm_GasUsed (g + static_gas BaseFee) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_BlobHash:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         index = w2n (HD ss) ∧
         g + static_gas BlobHash ≤ p.gasLimit))
  {(pc,BlobHash)}
  (evm_Stack ((if index < LENGTH t.blobHashes
               then EL index t.blobHashes else 0w):: TL ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode BlobHash)) *
   evm_GasUsed (g + static_gas BlobHash) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_BlobBaseFee:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas BlobBaseFee ≤ p.gasLimit))
  {(pc,BlobBaseFee)}
  (evm_Stack (n2w (t.baseFeePerBlobGas) :: ss) *
   evm_JumpDest j * evm_Exception e * evm_TxParams t *
   evm_PC (pc + LENGTH (opcode BlobBaseFee)) *
   evm_GasUsed (g + static_gas BlobBaseFee) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Pop:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧ g + static_gas Pop ≤ p.gasLimit))
    {(pc,Pop)}
    (evm_Stack (TL ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Pop)) *
     evm_GasUsed (g + static_gas Pop) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_MLoad:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         offset = w2n (HD ss) ∧
         g + static_gas MLoad + memory_cost m offset 32 ≤ p.gasLimit ∧
         em = expanded_memory m offset 32))
  {(pc,MLoad)}
  (evm_Stack (word_of_bytes F 0w (REVERSE (buffer_take offset 32 em))
              :: TL ss) *
   evm_JumpDest j * evm_Exception e * evm_Memory em *
   evm_PC (pc + LENGTH (opcode MLoad)) *
   evm_GasUsed (g + static_gas MLoad + memory_cost m offset 32) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_MStore:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧
         bytes = REVERSE (word_to_bytes (EL 1 ss) F) ∧
         g + static_gas MStore + memory_cost m offset 32 ≤ p.gasLimit ∧
         em = expanded_memory m offset 32))
  {(pc,MStore)}
  (evm_Stack (DROP 2 ss) *
   evm_PC (pc + LENGTH (opcode MStore)) *
   evm_JumpDest j * evm_Exception e *
   evm_Memory (buffer_write offset bytes em) *
   evm_GasUsed (g + static_gas MStore + memory_cost m offset 32) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_MStore8:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧
         bytes = [w2w (EL 1 ss)] ∧
         g + static_gas MStore8 + memory_cost m offset 1 ≤ p.gasLimit ∧
         em = expanded_memory m offset 1))
  {(pc,MStore8)}
  (evm_Stack (DROP 2 ss) *
   evm_PC (pc + LENGTH (opcode MStore8)) *
   evm_JumpDest j * evm_Exception e *
   evm_Memory (buffer_write offset bytes em) *
   evm_GasUsed (g + static_gas MStore8 + memory_cost m offset 1) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SLoad:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb * evm_Msdomain d *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         key = HD ss ∧
         sk = SK p.callee key ∧
         access_slot_check d sk ∧
         g + access_slot_cost rb sk ≤ p.gasLimit))
  {(pc,SLoad)}
  (evm_Stack (lookup_storage key
               (lookup_account p.callee rb.accounts).storage :: TL ss) *
   evm_PC (pc + LENGTH (opcode SLoad)) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + access_slot_cost rb sk) *
   evm_Rollback (accesses_add_slot sk rb) *
   evm_Msdomain (msdomain_add_slot sk d) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_SStore:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb * evm_Msdomain d *
   evm_AddRefund ar * evm_SubRefund sr * evm_Contexts cs * evm_CachedRB cb *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         key = HD ss ∧ value = EL 1 ss ∧
         ~p.static ∧ call_stipend < p.gasLimit - g ∧
         sk = SK p.callee key ∧ access_slot_check d sk ∧
         (orig_rb = if NULL cs then cb else SND (LAST cs)) ∧
         (cost,ad,sd) =
           SStore_gas orig_rb.accounts rb p.callee key value ∧
         g + cost ≤ p.gasLimit))
  {(pc,SStore)}
  (evm_Stack (DROP 2 ss) *
   evm_PC (pc + LENGTH (opcode SStore)) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + cost) *
   evm_Rollback (SStore_write p.callee key value $ accesses_add_slot sk rb) *
   evm_Msdomain (msdomain_add_slot sk d) *
   evm_AddRefund (ar + ad) *
   evm_SubRefund (sr + sd) *
   evm_Contexts cs *
   evm_CachedRB cb *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Jump:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (ss ≠ [] ∧ ISL e ∧
         w2n (HD ss) < LENGTH p.code ∧
         FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest ∧
         g + static_gas Jump ≤ p.gasLimit))
  {(pc,Jump)}
  (evm_Stack (TL ss) *
   evm_PC (w2n (HD ss)) *
   evm_JumpDest NONE * evm_Exception e *
   evm_GasUsed (g + static_gas Jump) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_JumpI:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (2 ≤ LENGTH ss ∧ ISL e ∧
         (if EL 1 ss = 0w then pc' = pc + LENGTH (opcode JumpI)
          else pc' = w2n (HD ss) ∧ w2n (HD ss) < LENGTH p.code ∧
               FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest) ∧
         g + static_gas JumpI ≤ p.gasLimit))
  {(pc,JumpI)}
  (evm_Stack (DROP 2 ss) *
   evm_PC pc' *
   evm_JumpDest NONE * evm_Exception e *
   evm_GasUsed (g + static_gas JumpI) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_JumpI_take:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond
     (2 ≤ LENGTH ss ∧ ISL e ∧
      EL 1 ss ≠ 0w ∧
      w2n (HD ss) < LENGTH p.code ∧
      FLOOKUP p.parsed (w2n (HD ss)) = SOME JumpDest ∧
      g + static_gas JumpI ≤ p.gasLimit))
  {(pc,JumpI)}
  (evm_Stack (DROP 2 ss) * evm_PC (w2n (HD ss)) * evm_JumpDest NONE *
   evm_Exception e * evm_GasUsed (g + static_gas JumpI) *
   evm_MsgParams p)
Proof
  mp_tac (GEN_ALL SPEC_JumpI)
  \\ rw[SPEC_MOVE_COND]
QED

Theorem SPEC_JumpI_skip:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond
     (2 ≤ LENGTH ss ∧ ISL e ∧
      EL 1 ss = 0w ∧
      g + static_gas JumpI ≤ p.gasLimit))
  {(pc,JumpI)}
  (evm_Stack (DROP 2 ss) *
   evm_PC (pc + LENGTH (opcode JumpI)) *
   evm_JumpDest NONE *
   evm_Exception e * evm_GasUsed (g + static_gas JumpI) *
   evm_MsgParams p)
Proof
  mp_tac (GEN_ALL SPEC_JumpI)
  \\ rw[SPEC_MOVE_COND]
QED

Theorem SPEC_PC:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (LENGTH ss < stack_limit  ∧ j = NONE ∧ ISL e ∧
           g + static_gas PC ≤ p.gasLimit))
    {(pc,PC)}
    (evm_Stack (n2w pc :: ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode PC)) *
     evm_GasUsed (g + static_gas PC) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_MSize:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e * evm_Memory m *
     cond (LENGTH ss < stack_limit  ∧ j = NONE ∧ ISL e ∧
           g + static_gas MSize ≤ p.gasLimit))
    {(pc,MSize)}
    (evm_Stack (n2w (buffer_length m) :: ss) *
     evm_JumpDest j * evm_Exception e * evm_Memory m *
     evm_PC (pc + LENGTH (opcode MSize)) *
     evm_GasUsed (g + static_gas MSize) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Gas:
  SPEC EVM_MODEL
    (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
     evm_JumpDest j * evm_Exception e *
     cond (LENGTH ss < stack_limit  ∧ j = NONE ∧ ISL e ∧
           g + static_gas Gas ≤ p.gasLimit))
    {(pc,Gas)}
    (evm_Stack (n2w (p.gasLimit - g - static_gas Gas) :: ss) *
     evm_JumpDest j * evm_Exception e *
     evm_PC (pc + LENGTH (opcode Gas)) *
     evm_GasUsed (g + static_gas Gas) * evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_JumpDest:
  SPEC EVM_MODEL
  (evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (j = NONE ∧ ISL e ∧ g + static_gas JumpDest ≤ p.gasLimit))
  {(pc,JumpDest)}
  (evm_PC (pc + LENGTH (opcode JumpDest)) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + static_gas JumpDest) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_TLoad:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb *
   cond (ss ≠ [] ∧ j = NONE ∧ ISL e ∧
         key = HD ss ∧
         g + warm_access_cost ≤ p.gasLimit))
  {(pc,TLoad)}
  (evm_Stack (lookup_storage key
               (lookup_transient_storage p.callee rb.tStorage) :: TL ss) *
   evm_PC (pc + LENGTH (opcode TLoad)) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + warm_access_cost) *
   evm_Rollback rb *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_TStore:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Rollback rb *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         key = HD ss ∧ value = EL 1 ss ∧
         ~p.static ∧ g + warm_access_cost ≤ p.gasLimit))
  {(pc,TStore)}
  (evm_Stack (DROP 2 ss) *
   evm_PC (pc + LENGTH (opcode TStore)) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + warm_access_cost) *
   evm_Rollback (rb with tStorage updated_by (λtStorage.
                 update_transient_storage p.callee
                   (update_storage key value
                     (lookup_transient_storage p.callee tStorage))
                 tStorage)) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_MCopy:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m *
   cond (3 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧
         sourceOffset = w2n (EL 1 ss) ∧
         sz = w2n (EL 2 ss) ∧
         max_expansion_range (offset,sz) (sourceOffset,sz) = (xOffset,xSize) ∧
         em = expanded_memory m xOffset xSize ∧
         g + MCopy_gas m xOffset xSize sz ≤ p.gasLimit))
  {(pc,MCopy)}
  (evm_Stack (DROP 3 ss) *
   evm_PC (pc + LENGTH (opcode MCopy)) *
   evm_JumpDest j * evm_Exception e *
   evm_Memory (MCopy_write em offset sourceOffset sz) *
   evm_GasUsed (g + MCopy_gas m xOffset xSize sz) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Push:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ j = NONE ∧ ISL e ∧
         g + static_gas (Push n bs) ≤ p.gasLimit))
  {(pc,Push n bs)}
  (evm_Stack (word_of_bytes F 0w (REVERSE bs) :: ss) *
   evm_PC (pc + LENGTH (opcode (Push n bs))) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + static_gas (Push n bs)) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Dup:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (LENGTH ss < stack_limit ∧ n < LENGTH ss ∧
         j = NONE ∧ ISL e ∧
         g + static_gas (Dup n) ≤ p.gasLimit))
  {(pc,Dup n)}
  (evm_Stack (EL n ss :: ss) *
   evm_PC (pc + LENGTH (opcode (Dup n))) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + static_gas (Dup n)) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Swap:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e *
   cond (SUC n < LENGTH ss ∧
         j = NONE ∧ ISL e ∧
         g + static_gas (Swap n) ≤ p.gasLimit))
  {(pc,Swap n)}
  (evm_Stack ([EL n (TL ss)] ++ TAKE n (TL ss) ++ [HD ss]
              ++ DROP (SUC n) (TL ss)) *
   evm_PC (pc + LENGTH (opcode (Swap n))) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + static_gas (Swap n)) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Log:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_JumpDest j * evm_Exception e * evm_Memory m * evm_Logs l *
   cond (2 + n ≤ LENGTH ss ∧
         offset = w2n (EL 0 ss) ∧
         sz = w2n (EL 1 ss) ∧
         j = NONE ∧ ISL e ∧
         ~p.static ∧
         ev = <|logger := p.callee; topics := TAKE n (DROP 2 ss);
                data := buffer_take offset sz em|> ∧
         dynamicGas = log_topic_cost * n + log_data_cost * sz +
                      memory_cost m offset sz ∧
         g + static_gas (Log n) + dynamicGas ≤ p.gasLimit ∧
         em = expanded_memory m offset sz))
  {(pc,Log n)}
  (evm_Stack (DROP (2 + n) ss) *
   evm_PC (pc + LENGTH (opcode (Log n))) *
   evm_JumpDest j * evm_Exception e *
   evm_GasUsed (g + static_gas (Log n) + dynamicGas) *
   evm_Memory em * evm_Logs (l ++ [ev]) *
   evm_MsgParams p)
Proof binop_tac
QED

Theorem SPEC_Create_fail:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Rollback rb * evm_Memory m * evm_Exception e * evm_ReturnData rd *
   evm_Contexts cs * evm_Msdomain d *
   cond ((if inst = Create2 then 4 else 3) ≤ LENGTH ss ∧ ISL e ∧
         value = w2n (EL 0 ss) ∧ offset = w2n (EL 1 ss) ∧ sz = w2n (EL 2 ss) ∧
         salt = EL 3 ss ∧
         em = expanded_memory m offset sz ∧
         (inst = Create ∨ inst = Create2) ∧
         gas = static_gas inst + init_code_word_cost * (word_size sz) +
               (if inst = Create2 then
                keccak256_per_word_cost * (word_size sz) else 0) +
               memory_cost m offset sz ∧
         code = buffer_take offset sz em ∧
         sender = lookup_account p.callee rb.accounts ∧
         addr = (if inst = Create2
                 then address_for_create2 p.callee salt code
                 else address_for_create p.callee sender.nonce) ∧
         LENGTH code ≤ 2 * max_code_size ∧
         gasLeft = p.gasLimit - g - gas ∧
         cappedGas = gasLeft - gasLeft DIV 64 ∧
         ¬p.static ∧
         (sender.balance < value ∨ SUC sender.nonce ≥ 2 ** 64 ∨
          SUC (LENGTH cs) > 1024) ∧
         g + gas + cappedGas ≤ p.gasLimit))
  {(pc,inst)}
  (evm_Stack (b2w F :: DROP (if inst = Create2 then 4 else 3) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + gas) * evm_MsgParams p *
   evm_Exception (INL ()) * evm_ReturnData [] *
   evm_Rollback rb * evm_Memory em * evm_Contexts cs *
   evm_Msdomain d)
Proof
  qmatch_goalsub_abbrev_tac`~_ ∧ djs ∧ _`
  \\ qmatch_goalsub_abbrev_tac`em = _ ∧ is_create ∧ _`
  \\ irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ qpat_x_assum`djs`mp_tac
  \\ qpat_x_assum`is_create`mp_tac
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ strip_tac
  \\ `step_inst inst = step_create (inst = Create2)` by (
       gvs[Abbr`is_create`, step_inst_def] )
  \\ `(if inst = Create2 then Create2 else Create) = inst`
     by gs[Abbr`is_create`]
  \\ qpat_x_assum`is_create`mp_tac
  \\ qmatch_asmsub_abbrev_tac`largs ≤ LENGTH ss`
  \\ `1 < largs ∧ 2 < largs ∧ (inst = Create2 ⇒ 3 < largs)` by rw[Abbr`largs`]
  \\ gvs[step_create_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def,
         set_current_context_def, consume_gas_def, EL_TAKE,
         read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, memory_expansion_info_split,
         expand_memory_split,get_gas_left_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ gvs[assert_not_static_def, get_static_def, bind_def, ignore_bind_def,
         assert_def, return_def, get_current_context_def, set_return_data_def,
         set_current_context_def, get_num_contexts_def, access_storage_split,
         HD_TAKE]
  \\ ntac 2 strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ `is_call inst` by gvs[Abbr`is_create`,is_call_def]
  \\ qpat_x_assum`is_create`mp_tac
  \\ gvs[abort_unuse_def, unuse_gas_def, bind_def, ignore_bind_def,
         return_def, fail_def, assert_def, get_current_context_def,
         set_current_context_def, push_stack_def, inc_pc_def,
         inc_pc_or_jump_def]
  \\ strip_tac
  \\ conj_tac >-
       (qpat_x_assum ‘{_ } = _’ $ rewrite_tac o single
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ end_tac
QED

Theorem SPEC_Create_fail_created:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Rollback rb * evm_Memory m * evm_Exception e * evm_ReturnData rd *
   evm_Contexts cs * evm_Msdomain d *
   cond ((if inst = Create2 then 4 else 3) ≤ LENGTH ss ∧ ISL e ∧
         value = w2n (EL 0 ss) ∧ offset = w2n (EL 1 ss) ∧ sz = w2n (EL 2 ss) ∧
         salt = EL 3 ss ∧
         em = expanded_memory m offset sz ∧
         (inst = Create ∨ inst = Create2) ∧
         gas = static_gas inst + init_code_word_cost * (word_size sz) +
               (if inst = Create2 then
                keccak256_per_word_cost * (word_size sz) else 0) +
               memory_cost m offset sz ∧
         code = buffer_take offset sz em ∧
         sender = lookup_account p.callee rb.accounts ∧
         addr = (if inst = Create2
                 then address_for_create2 p.callee salt code
                 else address_for_create p.callee sender.nonce) ∧
         access_check d addr ∧
         LENGTH code ≤ 2 * max_code_size ∧
         gasLeft = p.gasLimit - g - gas ∧
         cappedGas = gasLeft - gasLeft DIV 64 ∧
         ¬p.static ∧
         value ≤ sender.balance ∧ SUC sender.nonce < 2 ** 64 ∧
         SUC (LENGTH cs) ≤ 1024 ∧
         account_already_created (lookup_account addr rb.accounts) ∧
         access_storage_check d addr ∧
         g + gas + cappedGas ≤ p.gasLimit))
  {(pc,inst)}
  (evm_Stack (b2w F :: DROP (if inst = Create2 then 4 else 3) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + gas + cappedGas) * evm_MsgParams p *
   evm_Exception (INL ()) * evm_ReturnData [] *
   evm_Rollback (accesses_add addr rb
                 with accounts updated_by increment_nonce p.callee) *
   evm_Memory em * evm_Contexts cs *
   evm_Msdomain (msdomain_add_storage addr $ msdomain_add addr d))
Proof
  qmatch_goalsub_abbrev_tac`em = _ ∧ is_create ∧ _`
  \\ irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ qpat_x_assum`is_create`mp_tac
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ strip_tac
  \\ `step_inst inst = step_create (inst = Create2)` by (
       gvs[Abbr`is_create`, step_inst_def] )
  \\ `(if inst = Create2 then Create2 else Create) = inst`
     by gs[Abbr`is_create`]
  \\ `is_call inst` by gs[Abbr`is_create`, is_call_def]
  \\ qpat_x_assum`is_create`mp_tac
  \\ qmatch_asmsub_abbrev_tac`largs ≤ LENGTH ss`
  \\ `1 < largs ∧ 2 < largs ∧ (inst = Create2 ⇒ 3 < largs)` by rw[Abbr`largs`]
  \\ gvs[step_create_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def,
         set_current_context_def, consume_gas_def, EL_TAKE,
         read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, memory_expansion_info_split,
         expand_memory_split,get_gas_left_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ gvs[assert_not_static_def, get_static_def, bind_def, ignore_bind_def,
         assert_def, return_def, get_current_context_def, set_return_data_def,
         set_current_context_def, get_num_contexts_def, access_storage_split,
         abort_create_exists_def, update_accounts_def, HD_TAKE,
         fail_def, assert_def, get_current_context_def,
         set_current_context_def, push_stack_def, inc_pc_def,
         inc_pc_or_jump_def]
  \\ gvs[access_address_split, access_storage_split]
  \\ strip_tac
  \\ conj_tac >- simp[Abbr`cappedGas`,Abbr`gasLeft`]
  \\ conj_tac >-
       (qpat_x_assum ‘{_} = _’ $ rewrite_tac o single
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ end_tac
QED

Theorem SPEC_Create:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Rollback rb * evm_Memory m * evm_Exception e * evm_ReturnData rd *
   evm_Contexts cs * evm_Msdomain d * evm_JumpDest j *
   evm_CachedRB cb *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_Parsed pc inst * evm_hide_Parsed (all_pcs DELETE pc) *
   cond ((if inst = Create2 then 4 else 3) ≤ LENGTH ss ∧ ISL e ∧
         value = w2n (EL 0 ss) ∧ offset = w2n (EL 1 ss) ∧ sz = w2n (EL 2 ss) ∧
         salt = EL 3 ss ∧
         em = expanded_memory m offset sz ∧
         (inst = Create ∨ inst = Create2) ∧
         gas = static_gas inst + init_code_word_cost * (word_size sz) +
               (if inst = Create2 then
                keccak256_per_word_cost * (word_size sz) else 0) +
               memory_cost m offset sz ∧
         code = buffer_take offset sz em ∧
         sender = lookup_account p.callee rb.accounts ∧
         addr = (if inst = Create2
                 then address_for_create2 p.callee salt code
                 else address_for_create p.callee sender.nonce) ∧
         access_check d addr ∧
         LENGTH code ≤ 2 * max_code_size ∧
         gasLeft = p.gasLimit - g - gas ∧
         cappedGas = gasLeft - gasLeft DIV 64 ∧
         ¬p.static ∧
         value ≤ sender.balance ∧ SUC sender.nonce < 2 ** 64 ∧
         SUC (LENGTH cs) ≤ 1024 ∧
         ¬account_already_created (lookup_account addr rb.accounts) ∧
         access_storage_check d addr ∧
         new_parsed = parse_code 0 FEMPTY code ∧
         all_pcs = FDOM p.parsed ∪ FDOM new_parsed ∧
         g + gas + cappedGas ≤ p.gasLimit ∧
         tx = <|from := p.callee; to := SOME addr; value := value;
                gasLimit := cappedGas; data := []; nonce := 0; gasPrice := 0;
                accessList := []; blobVersionedHashes := [];
                maxFeePerGas := NONE; maxFeePerBlobGas := NONE;
                authorizationList := []|> ∧
         (orig_rb = if NULL cs then cb else SND (LAST cs)) ∧
         orig = update_account addr empty_account_state orig_rb.accounts ∧
         caller = <|stack := DROP (if inst = Create2 then 4 else 3) ss;
                    memory := em; pc := pc; jumpDest := j;
                    returnData := []; gasUsed := g + gas + cappedGas;
                    addRefund := ar; subRefund := sr; logs := l;
                    msgParams := p|> ∧
         caller_rb = accesses_add addr rb
                     with accounts updated_by increment_nonce p.callee ))
  {}
  (evm_Stack [] * evm_PC 0 * evm_GasUsed 0 *
   evm_MsgParams (initial_msg_params addr code F (Code addr) tx) *
   evm_JumpDest NONE *
   evm_Exception (INL ()) * evm_ReturnData [] *
   evm_Rollback (caller_rb with accounts updated_by
                 (transfer_value p.callee addr value o increment_nonce addr)) *
   evm_Memory empty_buffer *
   evm_AddRefund 0 * evm_SubRefund 0 * evm_Logs [] *
   CODE_POOL EVM_INSTR {(pc,inst) | FLOOKUP new_parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM new_parsed) *
   evm_Contexts (set_last_accounts orig $ (caller, cb) :: cs) *
   evm_CachedRB caller_rb *
   evm_Msdomain (msdomain_add_storage addr $ msdomain_add addr d))
Proof
  qmatch_goalsub_abbrev_tac`em = _ ∧ is_create ∧ _`
  \\ irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, STAR_evm_hide_Parsed,
                 CODE_POOL_EMPTY,STAR_CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ qpat_x_assum`is_create`mp_tac
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ strip_tac
  \\ `step_inst inst = step_create (inst = Create2)` by (
       gvs[Abbr`is_create`, step_inst_def] )
  \\ `(if inst = Create2 then Create2 else Create) = inst`
     by gs[Abbr`is_create`]
  \\ `is_call inst` by gs[Abbr`is_create`, is_call_def]
  \\ qpat_x_assum`is_create`mp_tac
  \\ qmatch_asmsub_abbrev_tac`largs ≤ LENGTH ss`
  \\ `1 < largs ∧ 2 < largs ∧ (inst = Create2 ⇒ 3 < largs)` by rw[Abbr`largs`]
  \\ gvs[step_create_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def,
         set_current_context_def, consume_gas_def, EL_TAKE,
         read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, memory_expansion_info_split,
         expand_memory_split,get_gas_left_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ gvs[assert_not_static_def, get_static_def, bind_def, ignore_bind_def,
         assert_def, return_def, get_current_context_def, set_return_data_def,
         set_current_context_def, get_num_contexts_def, access_storage_split,
         HD_TAKE, proceed_create_def,
         update_accounts_def, get_rollback_def, get_original_def,
         set_original_def, push_context_def, inc_pc_or_jump_def]
  \\ gvs[access_address_split, access_storage_split]
  \\ strip_tac
  \\ conj_tac >- gvs[Abbr`cappedGas`,Abbr`gasLeft`]
  \\ conj_tac >- (gvs[SUBSET_DEF, PULL_EXISTS,Abbr`all_pcs`,TO_FLOOKUP]
                  \\ metis_tac[NOT_SOME_NONE])
  \\ conj_tac >- simp[initial_msg_params_def]
  \\ conj_tac >- (gvs[SUBSET_DEF, PULL_EXISTS,Abbr`all_pcs`,TO_FLOOKUP]
                  \\ metis_tac[NOT_SOME_NONE])
  \\ conj_tac >- (
       simp[Abbr`orig`, Abbr`caller_rb`, Abbr`caller`, Abbr`orig_rb`,
            LAST_CONS_cond, NULL_EQ, Abbr`cb`]
       \\ qmatch_goalsub_abbrev_tac`_ a1 _ = _ a2 _`
       \\ `a1 = a2` by (rw[Abbr`a1`, Abbr`a2`,Abbr`rb`] \\ gvs[])
       \\ simp[] \\ AP_TERM_TAC \\ simp[]
       \\ simp[context_component_equality]
       \\ simp[Abbr`cappedGas`,Abbr`gasLeft`])
  \\ gs[EMPTY_evm2set]
  \\ conj_tac >-
      (qpat_x_assum ‘_ = {}’ mp_tac
       \\ fs [EXTENSION, Abbr`all_pcs`]
       \\ srw_tac[DNF_ss][TO_FLOOKUP]
       \\ eq_tac \\ rw []
       \\ first_x_assum(qspec_then`x`mp_tac)
       \\ simp[]
       \\ strip_tac \\ gvs[FORALL_PROD, TO_FLOOKUP]
       \\ metis_tac[option_CASES])
  \\ irule UPDATE_evm2set_without
  \\ simp[]
  \\ gvs[Abbr`all_pcs`,TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
  \\ simp[initial_msg_params_def]
  \\ metis_tac[]
QED

Definition delegate_check_def:
  delegate_check c d rb dCost newRb newDom ⇔
  case get_delegate c
  of NONE => dCost = 0 ∧ newRb = rb ∧ newDom = d
   | SOME delegate =>
       access_check d delegate ∧
       dCost = access_cost rb delegate ∧
       newRb = accesses_add delegate rb ∧
       newDom = msdomain_add delegate d
End

Theorem SPEC_Call_fail_balance:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e *
   cond (7 ≤ LENGTH ss ∧ ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧ value = w2n (EL 2 ss) ∧
         argsOffset = w2n (EL 3 ss) ∧ argsSize = w2n (EL 4 ss) ∧
         retOffset = w2n (EL 5 ss) ∧ retSize = w2n (EL 6 ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         access_check d addr ∧
         toAccount = lookup_account addr rb.accounts ∧
         cCost = (if call_inst = Call ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + call_value_cost + cCost + dCost) =
             (dynamicGas, stipend) ∧
         g + static_gas call_inst + dynamicGas + mCost ≤ p.gasLimit ∧
         ¬p.static ∧
         call_has_value call_inst ∧
         sender = lookup_account p.callee rb.accounts ∧
         sender.balance < value))
  {(pc,call_inst)}
  (evm_Stack (b2w F :: DROP 7 ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + static_gas call_inst + dynamicGas + mCost - stipend) *
   evm_MsgParams p *
   evm_Memory em *
   evm_Rollback newRb *
   evm_Msdomain newDom *
   evm_Exception (INL ()) *
   evm_ReturnData [])
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `(_,_) = _` $ assume_tac o SYM
  \\ qpat_x_assum `(_,_) = _` $ assume_tac o SYM
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ `step_inst call_inst = step_call call_inst` by (
       qpat_x_assum`call_has_value _`mp_tac \\
       Cases_on`call_inst` \\ simp[step_inst_def, call_has_value_def] )
  \\ `stipend ≤ g + dynamicGas + mCost` by (
       qhdtm_x_assum`call_gas`mp_tac
       \\ qpat_x_assum`_ ≤ _.gasLimit`mp_tac
       \\ simp[call_value_cost_def, call_stipend_def, call_gas_def])
  \\ `is_call call_inst` by (
       qpat_x_assum`call_has_value _`mp_tac \\
       Cases_on`call_inst` \\ simp[call_has_value_def, is_call_def])
  \\ `call_inst ≠ Call ⇒ cCost < value` by gvs[Abbr`cCost`]
  \\ Cases_on`call_inst = Call`
  \\ gvs[step_call_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, get_gas_left_def, HD_TAKE, option_CASE_rator,
         CaseEq"sum",CaseEq"prod",CaseEq"option",CaseEq"bool",fail_def,
         assert_not_static_def, get_static_def, abort_call_value_def, push_stack_def,
         set_return_data_def, unuse_gas_def, inc_pc_def, inc_pc_or_jump_def,
         Abbr`cCost`,delegate_check_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ (conj_tac >- simp[Abbr`em`, expanded_memory_def, memory_expand_by_def])
  \\ (conj_tac >-
        (qpat_x_assum ‘{_} = _’ $ rewrite_tac o single
         \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []))
  \\ end_tac
QED

Theorem SPEC_Call_fail_depth:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e * evm_Contexts cs *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         access_check d addr ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, stipend) ∧
         g + static_gas call_inst + dynamicGas + mCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         sender = lookup_account p.callee rb.accounts ∧
         value ≤ sender.balance ∧
         SUC (LENGTH cs) > 1024))
  {(pc,call_inst)}
  (evm_Stack (b2w F :: DROP (6 + vOff) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + static_gas call_inst + dynamicGas + mCost - stipend) *
   evm_MsgParams p *
   evm_Memory em *
   evm_Rollback newRb *
   evm_Msdomain newDom *
   evm_Exception (INL ()) *
   evm_Contexts cs *
   evm_ReturnData [])
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `(_,_) = _` $ assume_tac o SYM
  \\ qpat_x_assum `(_,_) = _` $ assume_tac o SYM
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ `step_inst call_inst = step_call call_inst` by (
       qpat_x_assum`is_call __`mp_tac \\
       Cases_on`call_inst` \\ simp[step_inst_def, is_call_def]
       \\ fs[])
  \\ `stipend ≤ g + dynamicGas + mCost` by (
       qhdtm_x_assum`call_gas`mp_tac
       \\ qpat_x_assum`_ ≤ _.gasLimit`mp_tac
       \\ Cases_on`value = 0` >- gvs[call_gas_def]
       \\ simp[call_value_cost_def, call_stipend_def, call_gas_def, Abbr`vCost`])
  \\ gvs[step_call_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, get_gas_left_def, HD_TAKE, option_CASE_rator,
         CaseEq"prod", sum_CASE_rator, prod_CASE_rator]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ qmatch_asmsub_rename_tac`option_CASE (get_delegate _) _ _ = (gdr,gds)`
  \\ reverse $ Cases_on`gdr` \\ gvs[]
  >- gvs[CaseEq"prod",CaseEq"sum",CaseEq"option",delegate_check_def,
         access_address_split]
  \\ qmatch_asmsub_abbrev_tac`access_address _ s4`
  \\ sg `gds.contexts = s4.contexts`
  >- (
    qpat_x_assum`_ gds = _`kall_tac
    \\ gvs[CaseEq"option"]
    \\ qpat_x_assum`_ (access_address _ _) _ = _`mp_tac
    \\ CASE_TAC \\ CASE_TAC
    \\ drule access_address_contexts_unchanged
    \\ rw[] \\ rw[] )
  \\ qmatch_asmsub_rename_tac`option_CASE (get_delegate _) _ _ = (INL gdr,_)`
  \\ PairCases_on`gdr`
  \\ gvs[get_current_context_def,bind_def,Abbr`s4`,return_def]
  \\ sg `dCost = gdr1`
  >- gvs[delegate_check_def,CaseEq"option",access_address_split]
  \\ gvs[get_current_context_def,return_def,bind_def,assert_def,
         set_current_context_def]
  \\ qmatch_asmsub_abbrev_tac`(COND a b c) (s1:execution_state)`
  \\ Q.SUBGOAL_THEN `(COND a b c) s1 = (INL (), s1)` assume_tac
  >- rw[Abbr`a`,Abbr`b`,Abbr`c`,return_def,assert_not_static_def,
        bind_def, ignore_bind_def, get_static_def, assert_def,
        get_current_context_def,Abbr`s1`]
  \\ gvs[Abbr`s1`,bind_def,ignore_bind_def,set_return_data_def,get_current_context_def,
         return_def,set_current_context_def,get_num_contexts_def,abort_unuse_def,
         unuse_gas_def,assert_def, push_stack_def, inc_pc_def, inc_pc_or_jump_def,
         Abbr`c`,delegate_check_def]
  \\ conj_tac >- simp[Abbr`em`, expanded_memory_def, memory_expand_by_def]
  \\ conj_tac >- gvs[CaseEq"option",access_address_split]
  \\ conj_tac >- gvs[CaseEq"option",access_address_split]
  \\ conj_tac >-
       (qpat_x_assum ‘{_} = _’ $ rewrite_tac o single
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ gvs[CaseEq"option",access_address_split]
  \\ end_tac
QED

Theorem SPEC_Call:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_JumpDest j * evm_Exception e * evm_CachedRB cb * evm_Contexts cs *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_Parsed pc call_inst * evm_hide_Parsed (all_pcs DELETE pc) *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         access_check d addr ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         calleeCode = (case get_delegate toAccount.code of
                         NONE => toAccount.code
                       | SOME del => (lookup_account del rb.accounts).code) ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, stipend) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         sender = lookup_account p.callee rb.accounts ∧
         value ≤ sender.balance ∧
         LENGTH cs < 1024 ∧
         data = buffer_take argsOffset argsSize em ∧
         callee = (if call_inst = CallCode ∨ call_inst = DelegateCall
                   then p.callee else addr) ∧
         tx = <|from := if call_inst = DelegateCall then p.caller else p.callee;
                to := SOME callee;
                value := if call_inst = DelegateCall then p.value else value;
                gasLimit := stipend; data := data; nonce := 0; gasPrice := 0;
                accessList := []; blobVersionedHashes := [];
                maxFeePerGas := NONE; maxFeePerBlobGas := NONE;
                authorizationList := []|> ∧
         ¬fIN addr precompile_addresses ∧
         new_parsed = parse_code 0 FEMPTY calleeCode ∧
         all_pcs = FDOM p.parsed ∪ FDOM new_parsed ∧
         caller = <|stack := DROP (6 + vOff) ss; memory := em; pc := pc; jumpDest := j;
                    returnData := []; gasUsed := g + gasCost; addRefund := ar;
                    subRefund := sr; logs := l; msgParams := p|>))
  {}
  (evm_Stack [] * evm_PC 0 * evm_GasUsed 0 *
   evm_MsgParams (initial_msg_params callee calleeCode
                  (call_inst = StaticCall ∨ p.static)
                  (Memory <|offset := retOffset; size := retSize|>) tx) *
   evm_Memory empty_buffer *
   evm_AddRefund 0 * evm_SubRefund 0 * evm_Logs [] *
   evm_JumpDest NONE *
   CODE_POOL EVM_INSTR {(pc,inst) | FLOOKUP new_parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM new_parsed) *
   evm_Contexts ((caller,cb) :: cs) *
   evm_CachedRB newRb *
   evm_Rollback (newRb with accounts updated_by
                 (if call_inst ≠ CallCode ∧ 0 < value
                  then transfer_value p.callee addr value
                  else I)) *
   evm_Msdomain newDom *
   evm_Exception (INL ()) *
   evm_ReturnData [])
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, STAR_evm_hide_Parsed,
                 STAR_CODE_POOL_evm2set, CODE_POOL_EMPTY]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `(_,_) = _` $ assume_tac o SYM
  \\ qpat_x_assum `(_,_) = _` $ assume_tac o SYM
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ `step_inst call_inst = step_call call_inst` by (
       qpat_x_assum`is_call __`mp_tac \\
       Cases_on`call_inst` \\ simp[step_inst_def, is_call_def]
       \\ fs[])
  \\ `g + dynamicGas + mCost + static_gas call_inst ≤ p.gasLimit`
     by gvs[Abbr`gasCost`]
  \\ gvs[step_call_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, get_gas_left_def, HD_TAKE, option_CASE_rator,
         CaseEq"prod", sum_CASE_rator, prod_CASE_rator]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ qmatch_asmsub_rename_tac`option_CASE (get_delegate _) _ _ = (gdr,gds)`
  \\ reverse $ Cases_on`gdr` \\ gvs[]
  >- gvs[CaseEq"prod",CaseEq"sum",CaseEq"option",delegate_check_def,
         access_address_split]
  \\ qmatch_asmsub_abbrev_tac`access_address _ s4`
  \\ sg `gds.contexts = s4.contexts`
  >- (
    qpat_x_assum`_ gds = _`kall_tac
    \\ gvs[CaseEq"option"]
    \\ qpat_x_assum`_ (access_address _ _) _ = _`mp_tac
    \\ CASE_TAC \\ CASE_TAC
    \\ drule access_address_contexts_unchanged
    \\ rw[] \\ rw[] )
  \\ qmatch_asmsub_rename_tac`option_CASE (get_delegate _) _ _ = (INL gdr,_)`
  \\ PairCases_on`gdr`
  \\ gvs[get_current_context_def,bind_def,Abbr`s4`,return_def]
  \\ sg `dCost = gdr1`
  >- gvs[delegate_check_def,CaseEq"option",access_address_split]
  \\ gvs[get_current_context_def,return_def,bind_def,assert_def,
         set_current_context_def]
  \\ qmatch_asmsub_abbrev_tac`(COND a b c) (s1:execution_state)`
  \\ Q.SUBGOAL_THEN `(COND a b c) s1 = (INL (), s1)` assume_tac
  >- rw[Abbr`a`,Abbr`b`,Abbr`c`,return_def,assert_not_static_def,
        bind_def, ignore_bind_def, get_static_def, assert_def,
        get_current_context_def,Abbr`s1`]
  \\ gvs[Abbr`s1`,bind_def,ignore_bind_def, set_return_data_def,
         get_current_context_def,return_def,set_current_context_def,
         get_num_contexts_def,abort_unuse_def,unuse_gas_def,assert_def,
         push_stack_def,inc_pc_def, inc_pc_or_jump_def,Abbr`c`,
         proceed_call_def,get_rollback_def,read_memory_def]
  \\ pop_assum kall_tac \\ qunabbrev_tac`b` \\ qunabbrev_tac`a`
  \\ qmatch_asmsub_abbrev_tac`(COND a b c) (s1:execution_state)`
  \\ qmatch_goalsub_abbrev_tac`_ with accounts updated_by f`
  \\ Q.SUBGOAL_THEN `(COND a b c) s1 = update_accounts f s1` assume_tac
  >- (rw[Abbr`a`,Abbr`b`,Abbr`c`,Abbr`f`,return_def,update_accounts_def,
         bind_def, ignore_bind_def, get_static_def, assert_def,
         get_current_context_def,Abbr`s1`,context_component_equality,
         execution_state_component_equality]
      \\ gvs[transfer_value_def, rollback_state_component_equality])
  \\ gvs[update_accounts_def, Abbr`s1`,Abbr`c`,return_def,
         get_caller_def,bind_def,ignore_bind_def,get_current_context_def,
         get_value_def,get_static_def,push_context_def]
  \\ pop_assum kall_tac
  \\ sg `gdr0 = calleeCode`
  >- gvs[delegate_check_def,CaseEq"option",access_address_split]
  \\ gvs[]
  \\ conj_tac >- gvs[Abbr`em`, expanded_memory_def, memory_expand_by_def]
  \\ gvs[SUBSET_DEF, PULL_EXISTS,Abbr`all_pcs`,initial_msg_params_def,
         TO_FLOOKUP]
  \\ conj_tac >- metis_tac[NOT_SOME_NONE]
  \\ conj_tac >- metis_tac[NOT_SOME_NONE]
  \\ conj_tac >-
       simp[Abbr`caller`,Abbr`em`, expanded_memory_def, memory_expand_by_def,
            context_component_equality,Abbr`gasCost`]
  \\ gvs[EMPTY_evm2set]
  \\ conj_tac >- gvs[CaseEq"option",access_address_split,delegate_check_def]
  \\ conj_tac >- gvs[CaseEq"option",access_address_split,delegate_check_def]
  \\ conj_tac >-
      (qpat_x_assum ‘_ = {}’ mp_tac
       \\ fs [EXTENSION]
       \\ srw_tac[DNF_ss][TO_FLOOKUP]
       \\ eq_tac \\ rw []
       \\ first_x_assum(qspec_then`x`mp_tac)
       \\ simp[]
       \\ rw[]
       \\ metis_tac[option_CASES])
  \\ irule UPDATE_evm2set_without
  \\ simp[]
  \\ gvs[TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
  \\ simp[initial_msg_params_def]
  \\ gvs[CaseEq"option",access_address_split,delegate_check_def]
  \\ metis_tac[]
QED

Theorem call_gas_cost_covers_stipend:
  call_gas value gas gasLeft mCost
    (accessCost + (if 0 < value then call_value_cost else 0) + cCost + dCost) =
      (dynamicGas,stipend) ==>
  stipend <= staticCost + dynamicGas + mCost
Proof
  strip_tac >>
  `stipend <= dynamicGas + mCost` suffices_by decide_tac >>
  irule call_gas_stipend_le_consumed >>
  goal_assum (drule_at Any) >>
  Cases_on `0 < value` >> simp[call_value_cost_def, call_stipend_def]
QED

Theorem call_stack_after_pop_has_room[local]:
  LENGTH ss <= stack_limit /\ 6 + vOff <= LENGTH ss ==>
  LENGTH (DROP (6 + vOff) ss) < stack_limit
Proof
  simp[LENGTH_DROP] >> decide_tac
QED

Theorem call_static_check_success[local]:
  s.contexts = (ctxt,cb)::cs /\ ctxt.msgParams = p /\
  (0 < (value:num) ==> ~p.static) ==>
  (if op = Call /\ 0 < value then assert_not_static else return ()) s =
    (INL (),s)
Proof
  strip_tac >> Cases_on `op = Call /\ 0 < value` >>
  simp[assert_not_static_def, get_static_def, get_current_context_def,
       assert_def, bind_def, return_def]
QED

Theorem step_call_prepared:
  s.contexts = (caller,cb)::cs /\ s.rollback = rb /\ s.msdomain = d /\
  caller.stack = ss /\ caller.msgParams = p /\
  caller.memory = m /\ caller.gasUsed = g /\
  6 + vOff <= LENGTH ss /\
  vOff = (if call_has_value op then 1 else 0) /\
  gas = w2n (EL 0 ss) /\ addr = w2w (EL 1 ss) /\
  value = (if 0 < vOff then w2n (EL 2 ss) else 0) /\
  argsOffset = w2n (EL (vOff + 2) ss) /\
  argsSize = w2n (EL (vOff + 3) ss) /\
  retOffset = w2n (EL (vOff + 4) ss) /\
  retSize = w2n (EL (vOff + 5) ss) /\
  max_expansion_range (argsOffset,argsSize) (retOffset,retSize) = (offset,sz) /\
  em = expanded_memory m offset sz /\ access_check d addr /\
  toAccount = lookup_account addr rb.accounts /\
  vCost = (if 0 < value then call_value_cost else 0) /\
  cCost = (if op = Call /\ 0 < value /\ account_empty toAccount
           then new_account_cost else 0) /\
  delegate_check toAccount.code (msdomain_add addr d)
    (accesses_add addr rb) dCost newRb newDom /\
  calleeCode = (case get_delegate toAccount.code of
    NONE => toAccount.code | SOME del => (lookup_account del rb.accounts).code) /\
  mCost = memory_cost m offset sz /\
  call_gas value gas (p.gasLimit - g) mCost
    (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas,stipend) /\
  gasCost = static_gas op + dynamicGas + mCost /\
  g + gasCost <= p.gasLimit /\
  (0 < value ==> ~p.static) /\
  value <= (lookup_account p.callee rb.accounts).balance /\ LENGTH cs < 1024 ==>
  step_call op s =
  proceed_call op p.callee addr value argsOffset argsSize calleeCode stipend
    (Memory <|offset := retOffset; size := retSize|>)
    (s with <|rollback := newRb; msdomain := newDom;
      contexts := (caller with <|stack := DROP (6 + vOff) ss;
        memory := em; gasUsed := g + gasCost; returnData := []|>,cb)::cs|>)
Proof
  strip_tac >>
  `vOff <= 1` by (Cases_on `call_has_value op` >> simp[]) >>
  `0 < 6 + vOff /\ 1 < 6 + vOff /\ 2 < 6 + vOff /\
   vOff + 2 < 6 + vOff /\ vOff + 3 < 6 + vOff /\
   vOff + 4 < 6 + vOff /\ vOff + 5 < 6 + vOff` by decide_tac >>
  pure_rewrite_tac[step_call_def] >>
  qpat_assum `vOff = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  pure_rewrite_tac[LET_THM, pop_stack_def, bind_def, ignore_bind_def,
    get_current_context_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `caller.stack = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `6 + vOff <= _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [assert_def, return_def, bind_def,
    ignore_bind_def, set_current_context_def] >>
  pure_rewrite_tac[get_current_context_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [return_def] >>
  qpat_assum `caller.stack = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `6 + vOff <= _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [return_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  simp_tac (srw_ss()) [EL_TAKE, arithmeticTheory.ADD_COMM,
    DECIDE ``!n:num. 0 < 6 + n /\ 1 < 6 + n /\ 2 < 6 + n /\
      2 + n < 6 + n /\ 3 + n < 6 + n /\ 4 + n < 6 + n /\ 5 + n < 6 + n``] >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[GSYM th]))
    [`gas = _`, `addr = _`, `value = _`, `argsOffset = _`, `argsSize = _`,
     `retOffset = _`, `retSize = _`] >>
  qpat_assum `max_expansion_range _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  simp_tac (srw_ss()) [HD_TAKE, DECIDE ``!n:num. 0 < n + 6``] >>
  qpat_assum `gas = _` (fn th => pure_rewrite_tac[GSYM (REWRITE_RULE[EL] th)]) >>
  simp_tac (srw_ss()) [memory_expansion_info_def, bind_def, LET_THM,
    get_current_context_def, return_def] >>
  qpat_assum `caller.memory = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `mCost = _` (fn th => pure_rewrite_tac[GSYM (REWRITE_RULE[memory_cost_def] th)]) >>
  pure_rewrite_tac[bind_def] >>
  qpat_assum `access_check _ _` (fn th =>
    simp_tac (srw_ss()) [access_address_split, th]) >>
  qpat_assum `s.rollback = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `s.msdomain = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `access_check _ _` (fn th =>
    qpat_assum `s.msdomain = _` (fn td =>
    qpat_assum `s.rollback = _` (fn tr =>
      simp_tac (srw_ss()) [access_address_split, th, td, tr,
        get_accounts_def, return_def]))) >>
  qpat_assum `toAccount = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[GSYM th]))
    [`vCost = _`, `cCost = _`] >>
  qpat_x_assum `delegate_check _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[delegate_check_def] >>
  Cases_on `get_delegate toAccount.code` >>
  pure_rewrite_tac[option_CLAUSES] >> BETA_TAC >> strip_tac >>
  qpat_assum `s.rollback = _` (fn tr =>
    qpat_assum `s.msdomain = _` (fn td =>
    simp_tac (srw_ss()) [access_address_split, tr, td,
      return_def, bind_def])) >>
  qpat_assum `access_check _ _` (fn th =>
    qpat_assum `s.rollback = _` (fn tr =>
    qpat_assum `s.msdomain = _` (fn td =>
      simp_tac (srw_ss()) [access_address_split, th, tr, td,
        return_def, bind_def]))) >>
  qpat_assum `caller.msgParams = _` (fn tp =>
    qpat_assum `caller.gasUsed = _` (fn tg =>
    simp_tac (srw_ss()) [get_gas_left_def, get_current_context_def,
      bind_def, return_def, tp, tg])) >>
  qpat_assum `call_gas _ _ _ _ _ = _` (fn th =>
    qpat_assum `dCost = _` (fn td =>
      simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [td,
        AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] th,
        AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  qpat_assum `gasCost = _` (fn th => pure_rewrite_tac
    [GSYM (SIMP_RULE (srw_ss())
      [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] th)]) >>
  qpat_assum `g + gasCost <= _` (fn tb =>
    qpat_assum `caller.msgParams = _` (fn tp =>
    qpat_assum `caller.gasUsed = _` (fn tg =>
    simp_tac (srw_ss()) [consume_gas_def, LET_THM, get_current_context_def,
      bind_def, ignore_bind_def, return_def, assert_def,
      set_current_context_def, tp, tg, tb]))) >>
  qmatch_goalsub_abbrev_tac
    `(if op = Call /\ 0 < value then assert_not_static else return ()) st` >>
  `(if op = Call /\ 0 < value then assert_not_static else return ()) st =
    (INL (),st)` by
    (irule call_static_check_success >>
     simp[Abbr `st`] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `(if _ then _ else _) st = _`
    (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [Abbr `st`] >>
  qpat_assum `caller.memory = _` (fn tm =>
    qpat_assum `caller.msgParams = _` (fn tp =>
    simp_tac (srw_ss()) [expand_memory_def, get_current_context_def,
      set_current_context_def, get_callee_def, bind_def, return_def, tm, tp])) >>
  `~((lookup_account p.callee rb.accounts).balance < value)` by decide_tac >>
  `~(1024 < SUC (LENGTH cs))` by decide_tac >>
  qpat_assum `~(_ < value)` (fn tb =>
    qpat_assum `~(1024 < _)` (fn td =>
    simp_tac (srw_ss()) [tb, td, LET_THM, set_return_data_def, get_num_contexts_def,
      get_current_context_def, set_current_context_def, bind_def, return_def])) >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[th]))
    [`newRb = _`, `newDom = _`, `s.rollback = _`, `s.msdomain = _`,
     `calleeCode = _`, `em = _`] >>
  simp_tac (srw_ss()) [expanded_memory_def, memory_expand_by_def] >>
  qpat_assum `~(1024 < _)` (fn td =>
    simp_tac (srw_ss()) [arithmeticTheory.GREATER_DEF, td]) >>
  AP_TERM_TAC >>
  qpat_assum `s.rollback = _` (fn tr =>
    qpat_assum `s.msdomain = _` (fn td =>
    simp_tac (srw_ss()) [execution_state_component_equality, tr, td]))
QED

Theorem proceed_call_precompile_success:
  s.contexts = (parent,prb)::rest /\ s.rollback = rb /\
  parent.msgParams.callee = sender /\
  data = buffer_take argsOffset argsSize parent.memory /\
  fIN addr precompile_addresses /\
  (!s ctxt crb rest.
    s.contexts = (ctxt,crb)::rest /\
    ctxt.msgParams.data = buffer_of_list data /\
    ctxt.msgParams.gasLimit = stipend /\
    ctxt.gasUsed = 0 /\ ctxt.returnData = [] ==>
    (dispatch_precompiles addr s : unit execution_result) =
      (INR NONE, s with contexts :=
        (ctxt with <|gasUsed := pg; returnData := out|>,crb)::rest)) ==>
  ?c. c.msgParams.outputTo = outputTo /\
      c.msgParams.gasLimit = stipend /\ c.gasUsed = pg /\
      c.returnData = out /\ c.logs = [] /\
      c.addRefund = 0 /\ c.subRefund = 0 /\
      proceed_call op sender addr value argsOffset argsSize code stipend outputTo s =
        (INR NONE, s with <|
          rollback := rb with accounts updated_by
            (if op <> CallCode /\ 0 < value
             then transfer_value sender addr value else I);
          contexts := (c,rb)::(parent,prb)::rest |> )
Proof
  strip_tac >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  simp[proceed_call_def, get_rollback_def, read_memory_def,
       update_accounts_def, get_caller_def, get_value_def, get_static_def,
       get_current_context_def, push_context_def,
       bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `CONS (ctxt,rb)` >>
  qmatch_goalsub_abbrev_tac `dispatch_precompiles addr ds` >>
  `ds.contexts = (ctxt,rb)::(parent,prb)::rest` by simp[Abbr `ds`] >>
  `ctxt.msgParams.data = buffer_of_list data /\
   ctxt.msgParams.gasLimit = stipend /\ ctxt.gasUsed = 0 /\
   ctxt.returnData = []` by
    simp[Abbr `ctxt`, initial_context_def, initial_msg_params_def] >>
  qpat_x_assum `!s ctxt crb rest. _` drule_all >>
  disch_then SUBST1_TAC >>
  qexists_tac `ctxt with <|gasUsed := pg; returnData := out|>` >>
  simp[Abbr `ctxt`, initial_context_def, initial_msg_params_def,
       Abbr `ds`, execution_state_component_equality,
       rollback_state_component_equality]
QED

Theorem handle_step_success_memory_exact:
  s.contexts = (c,crb)::(parent,prb)::rest /\
  c.msgParams.outputTo = Memory mr /\
  c.logs = [] /\ c.addRefund = 0 /\ c.subRefund = 0 /\
  c.msgParams.gasLimit - c.gasUsed <= parent.gasUsed /\
  LENGTH parent.stack < stack_limit ==>
  handle_step NONE s =
    (INL (), s with contexts :=
      (parent with <|
         gasUsed := parent.gasUsed - (c.msgParams.gasLimit - c.gasUsed);
         pc := parent.pc + 1; returnData := c.returnData;
         stack := 1w::parent.stack;
         memory := buffer_write mr.offset (TAKE mr.size c.returnData) parent.memory
       |>,prb)::rest)
Proof
  strip_tac >>
  simp[handle_step_def, handle_create_def, handle_exception_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       pop_context_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
       inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       get_current_context_def, set_current_context_def,
       handle_def, reraise_def, bind_def, ignore_bind_def, return_def,
       assert_def, stack_limit_def,
       execution_state_component_equality, context_component_equality]
QED

Theorem step_precompile_success_exact:
  wf_state s /\ s.contexts = (caller,cb)::cs /\
  s.rollback = rb /\ s.msdomain = d /\
  caller.stack = ss /\ caller.msgParams = p /\ caller.pc = pc /\
  caller.memory = m /\ caller.gasUsed = g /\
  FLOOKUP p.parsed pc = SOME op /\
  6 + vOff <= LENGTH ss /\
  vOff = (if call_has_value op then 1 else 0) /\
  gas = w2n (EL 0 ss) /\ addr = w2w (EL 1 ss) /\
  value = (if 0 < vOff then w2n (EL 2 ss) else 0) /\
  argsOffset = w2n (EL (vOff + 2) ss) /\
  argsSize = w2n (EL (vOff + 3) ss) /\
  retOffset = w2n (EL (vOff + 4) ss) /\
  retSize = w2n (EL (vOff + 5) ss) /\
  max_expansion_range (argsOffset,argsSize) (retOffset,retSize) = (offset,sz) /\
  em = expanded_memory m offset sz /\ access_check d addr /\
  toAccount = lookup_account addr rb.accounts /\
  vCost = (if 0 < value then call_value_cost else 0) /\
  cCost = (if op = Call /\ 0 < value /\ account_empty toAccount
           then new_account_cost else 0) /\
  delegate_check toAccount.code (msdomain_add addr d)
    (accesses_add addr rb) dCost newRb newDom /\
  mCost = memory_cost m offset sz /\
  call_gas value gas (p.gasLimit - g) mCost
    (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas,stipend) /\
  gasCost = static_gas op + dynamicGas + mCost /\
  g + gasCost <= p.gasLimit /\
  is_call op /\ op <> Create /\ op <> Create2 /\
  (0 < value ==> ~p.static) /\
  value <= (lookup_account p.callee rb.accounts).balance /\ LENGTH cs < 1024 /\
  data = buffer_take argsOffset argsSize em /\
  fIN addr precompile_addresses /\
  (!s ctxt crb rest.
    s.contexts = (ctxt,crb)::rest /\
    ctxt.msgParams.data = buffer_of_list data /\
    ctxt.msgParams.gasLimit = stipend /\
    ctxt.gasUsed = 0 /\ ctxt.returnData = [] ==>
    (dispatch_precompiles addr s : unit execution_result) =
      (INR NONE, s with contexts :=
        (ctxt with <|gasUsed := pg; returnData := out|>,crb)::rest)) ==>
  step s =
    (INL (),s with <|
      rollback := newRb with accounts updated_by
        (if op <> CallCode /\ 0 < value
         then transfer_value p.callee addr value else I);
      msdomain := newDom;
      contexts := (caller with <|
        stack := 1w::DROP (6 + vOff) ss; pc := pc + 1;
        gasUsed := g + gasCost - (stipend - pg);
        memory := buffer_write retOffset (TAKE retSize out) em;
        returnData := out|>,cb)::cs|>)
Proof
  strip_tac >>
  `LENGTH ss <= stack_limit` by
    (qpat_x_assum `wf_state s` mp_tac >>
     simp[wf_state_def, wf_context_def]) >>
  `LENGTH (DROP (6 + vOff) ss) < stack_limit` by
    (irule call_stack_after_pop_has_room >> simp[]) >>
  `stipend <= gasCost` by
    (qpat_assum `gasCost = _` (fn th => pure_rewrite_tac[th]) >>
     irule call_gas_cost_covers_stipend >>
     qpat_x_assum `call_gas _ _ _ _ _ = _` mp_tac >>
     qpat_assum `vCost = _` (fn th => pure_rewrite_tac[th]) >>
     strip_tac >> goal_assum (drule_at Any)) >>
  drule_all (PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES] (Q.INST
    [`calleeCode` |-> `case get_delegate toAccount.code of
      NONE => toAccount.code | SOME del => (lookup_account del rb.accounts).code`]
    step_call_prepared)) >>
  strip_tac >>
  qmatch_abbrev_tac `step s = final` >>
  qmatch_asmsub_abbrev_tac `proceed_call op _ _ _ _ _ code _ _ prepared` >>
  `prepared.contexts = (caller with <|stack := DROP (6 + vOff) ss;
    memory := em; gasUsed := g + gasCost; returnData := []|>,cb)::cs` by
    simp[Abbr `prepared`] >>
  `prepared.rollback = newRb` by simp[Abbr `prepared`] >>
  `(caller with <|stack := DROP (6 + vOff) ss;
    memory := em; gasUsed := g + gasCost; returnData := []|>).msgParams.callee = p.callee` by simp[] >>
  `data = buffer_take argsOffset argsSize
    (caller with <|stack := DROP (6 + vOff) ss;
    memory := em; gasUsed := g + gasCost; returnData := []|>).memory` by simp[] >>
  drule_all (Q.INST
    [`outputTo` |-> `Memory <|offset := retOffset; size := retSize|>`]
    proceed_call_precompile_success) >>
  disch_then (qspecl_then [`value`, `retSize`, `retOffset`, `op`, `code`] strip_assume_tac) >>
  qpat_x_assum `proceed_call _ _ _ _ _ _ _ _ _ _ = _` (fn th =>
    qpat_x_assum `step_call op s = _` (assume_tac o REWRITE_RULE [th])) >>
  qmatch_asmsub_abbrev_tac `step_call op s = (INR NONE, returned)` >>
  `returned.contexts = (c,newRb)::
    (caller with <|stack := DROP (6 + vOff) ss;
     memory := em; gasUsed := g + gasCost; returnData := []|>,cb)::cs` by
    simp[Abbr `returned`] >>
  drule (Q.INST [`s` |-> `returned`] handle_step_success_memory_exact) >>
  simp[] >>
  (impl_tac >- (fs[stack_limit_def] >> decide_tac)) >>
  disch_then (assume_tac o REWRITE_RULE []) >>
  `step_inst op = step_call op` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`op <> Create`, `op <> Create2`, `is_call op`] >>
     rpt (pop_assum kall_tac) >>
     Cases_on `op` >> simp[is_call_def, step_inst_def]) >>
  simp[step_def, handle_def, bind_def, ignore_bind_def, return_def, get_current_context_def] >>
  simp[Abbr `final`, Abbr `returned`, Abbr `prepared`,
       execution_state_component_equality, context_component_equality]
QED

(* A call to a precompile runs the precompile and returns to the caller in
   the same step. The rule takes the precompile's behaviour as a hypothesis:
   started on a fresh context holding the call data, it succeeds (finish),
   having used pg gas and produced output out, and changes nothing else. *)

(* Why it holds (a trace of the one step):
   - step_call pops the arguments, charges gasCost, expands memory to em and
     calls proceed_call exactly as in SPEC_Call (same hypotheses).
   - proceed_call pushes (initial_context callee calleeCode ... (Memory ...)
     tx, newRb) and, since fIN addr precompile_addresses, runs
     dispatch_precompiles addr on that state. The new context has
     msgParams.data = buffer_of_list data, gasLimit = stipend, gasUsed = 0 and
     returnData = [], so the hypothesis applies and the result is INR NONE.
   - step_inst raised, so inc_pc_or_jump does not run; handle_step NONE goes
     through handle_create (outputTo is Memory, so no effect) to
     handle_exception NONE. There are 2 + LENGTH cs contexts, so it pops the
     callee with success = T: unuse_gas (stipend - pg) (stipend ≤ gasCost by
     call_gas_def, so the assert holds), push_logs [], update_gas_refund
     (0,0), no rollback reset; then inc_pc, set_return_data out, push_stack
     1w (the stack fits: wf_state gives LENGTH ss ≤ stack_limit and 6 values
     were popped) and write_memory retOffset (TAKE retSize out). *)

Theorem SPEC_Call_precompile:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_JumpDest j * evm_Exception e * evm_CachedRB cb * evm_Contexts cs *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         access_check d addr ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, stipend) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         sender = lookup_account p.callee rb.accounts ∧
         value ≤ sender.balance ∧
         LENGTH cs < 1024 ∧
         data = buffer_take argsOffset argsSize em ∧
         fIN addr precompile_addresses ∧
         (∀s ctxt crb rest.
            s.contexts = (ctxt,crb)::rest ∧
            ctxt.msgParams.data = buffer_of_list data ∧
            ctxt.msgParams.gasLimit = stipend ∧
            ctxt.gasUsed = 0 ∧ ctxt.returnData = [] ⇒
            (dispatch_precompiles addr s : unit execution_result) =
            (INR NONE,
             s with contexts :=
               (ctxt with <|gasUsed := pg; returnData := out|>,crb)::rest))))
  {(pc,call_inst)}
  (evm_Stack (1w :: DROP (6 + vOff) ss) * evm_PC (pc + 1) *
   evm_GasUsed (g + gasCost - (stipend - pg)) * evm_MsgParams p *
   evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
   evm_Rollback (newRb with accounts updated_by
                 (if call_inst ≠ CallCode ∧ 0 < value
                  then transfer_value p.callee addr value
                  else I)) *
   evm_Msdomain newDom * evm_ReturnData out *
   evm_JumpDest j * evm_Exception e * evm_CachedRB cb * evm_Contexts cs *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l)
Proof
  irule IMP_EVM_SPEC >> rpt strip_tac >>
  rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, STAR_CODE_POOL_evm2set] >>
  qmatch_goalsub_abbrev_tac `b ==> _` >>
  reverse (Cases_on `b`) >- simp[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  full_simp_tac pure_ss [CODE_POOL_evm2set] >>
  `~ISR (FST s)` by
    (qpat_x_assum `ISL e` mp_tac >> simp[] >>
     Cases_on `FST s` >> simp[]) >>
  `(SND s).contexts =
    (FST (HD (SND s).contexts), SND (HD (SND s).contexts))::cs` by
    (Cases_on `(SND s).contexts` >> fs[wf_state_def]) >>
  rename1 `evm2set_without dom r = _` >>
  mp_tac (Q.INST [`s` |-> `SND (r : (unit + exception option) # execution_state)`,
    `caller` |-> `FST (HD (SND (r : (unit + exception option) # execution_state)).contexts)`, `op` |-> `call_inst`]
    step_precompile_success_exact) >>
  (impl_tac >- gvs[]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `step (SND r) = result` >>
  `wf_state (SND result)` by
    (qpat_x_assum `step (SND r) = result` (fn th =>
       pure_rewrite_tac[GSYM th]) >>
     irule step_preserves_wf_state >> simp[]) >>
  qexists_tac `result` >>
  simp[] >>
  conj_tac >-
    (simp[Abbr `result`] >>
     Cases_on `FST r` >> gvs[]) >>
  sym_tac >> irule UPDATE_evm2set_without >>
  gvs[Abbr `result`]
QED

Theorem witness_precompile_identity:
  fIN (4w:address) precompile_addresses ∧
  (pg = 15 + 3 * word_size (LENGTH data) ∧ pg ≤ stipend ⇒
   ∀s ctxt crb rest.
     s.contexts = (ctxt,crb)::rest ∧
     ctxt.msgParams.data = buffer_of_list data ∧
     ctxt.msgParams.gasLimit = stipend ∧
     ctxt.gasUsed = 0 ∧ ctxt.returnData = [] ⇒
     dispatch_precompiles 4w s =
     (INR NONE,
      s with contexts :=
        (ctxt with <|gasUsed := pg; returnData := data|>,crb)::rest))
Proof
  conj_tac >- (
    simp[precompile_addresses_def, finite_setTheory.fIN_fset_ABS] \\ EVAL_TAC)
  \\ rw[dispatch_precompiles_def,precompile_identity_def,get_call_data_def,
        bind_def,ignore_bind_def,get_current_context_def,return_def,
        consume_gas_def,assert_def,set_current_context_def,
        set_return_data_def,finish_def]
QED

Theorem SPEC_Return_outermost:
  SPEC EVM_MODEL
  (evm_Stack ss *
   evm_PC pc *
   evm_Contexts cs *
   evm_Memory m *
   evm_ReturnData rd *
   evm_MsgParams p *
   evm_GasUsed g *
   evm_Exception e *
   evm_Rollback rb *
   cond (2 ≤ LENGTH ss ∧ NULL cs ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧
         sz = w2n (EL 1 ss) ∧
         (inst = Return ∨ inst = Revert) ∧
         em = expanded_memory m offset sz ∧
         data = buffer_take offset sz em ∧
         gasCost = static_gas inst + memory_cost m offset sz + codeCost ∧
         returnCode = (inst = Return ∧ is_code_dest p.outputTo) ∧
         (if returnCode then
            (case data of [] => T | h::_ => h ≠ 239w) ∧
            (codeCost = code_deposit_cost * LENGTH data) ∧
            LENGTH data ≤ max_code_size
          else codeCost = 0) ∧
         g + gasCost ≤ p.gasLimit))
  {(pc,inst)}
  (evm_Stack (DROP 2 ss) *
   evm_ReturnData data *
   evm_PC pc *
   evm_Contexts cs *
   evm_Rollback (if returnCode then rb with accounts updated_by
                   (λaccounts.
                      update_account (case p.outputTo of Code addr => addr)
                        (lookup_account (case p.outputTo of Code addr => addr)
                           accounts with code := data) accounts)
                 else rb) *
   evm_Memory em *
   evm_MsgParams p *
   evm_GasUsed (g + gasCost) *
   evm_Exception (INR (if inst = Revert then SOME Reverted else NONE)))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ qmatch_asmsub_abbrev_tac`sz = _ ∧ is_ret ∧ _`
  \\ last_x_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ qpat_x_assum`is_ret`mp_tac
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ strip_tac
  \\ `step_inst inst = step_return (inst = Return)`
     by gvs[Abbr`is_ret`, step_inst_def]
  \\ qpat_x_assum`is_ret`mp_tac
  \\ gvs [step_return_def,bind_def,ignore_bind_def,pop_stack_def,
          get_current_context_def,return_def,assert_def,
          set_current_context_def,memory_expansion_info_def,
          consume_gas_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ qmatch_asmsub_abbrev_tac`COND b1 (INL _)`
  \\ `b1` by (
       qpat_x_assum`g + _ ≤ _`mp_tac
       \\ simp[Abbr`b1`, memory_cost_def, EL_TAKE, HD_TAKE, Abbr`gasCost`]
       \\ rw[] )
  \\ gvs[expand_memory_def,bind_def,ignore_bind_def,get_current_context_def,
         return_def,set_current_context_def,read_memory_def,set_return_data_def]
  \\ strip_tac
  \\ reverse $ gvs
       [Abbr`is_ret`,finish_def,revert_def,handle_step_def,handle_create_def,
        handle_def,bind_def,ignore_bind_def,reraise_def,get_return_data_def,
        get_current_context_def,return_def,get_output_to_def,EL_TAKE,HD_TAKE,
        return_destination_case_elim,handle_exception_def,get_num_contexts_def,
        NULL_EQ]
  >- (
    gvs[Abbr`em`, memory_cost_def, expanded_memory_def, memory_expand_by_def]
    \\ conj_tac >-
         (qpat_assum ‘{_} = _’ $ rewrite_tac o single o GSYM
          \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
    \\ end_tac)
  \\ Cases_on`p.outputTo` \\ gvs[reraise_def,return_def]
  >- (
    gvs[Abbr`em`, memory_cost_def, expanded_memory_def, memory_expand_by_def,
        Abbr`gasCost`,is_code_dest_def]
    \\ conj_tac >-
         (qpat_assum ‘{_} = _’ $ rewrite_tac o single o GSYM
          \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
    \\ end_tac)
  \\ gvs[ignore_bind_def,bind_def,assert_def,return_def,Abbr`em`,
         expanded_memory_def,memory_expand_by_def,is_code_dest_def,
         consume_gas_def,get_current_context_def,memory_cost_def,
         set_current_context_def,update_accounts_def,reraise_def]
  \\ conj_tac >-
       (qpat_assum ‘{_} = _’ $ rewrite_tac o single o GSYM
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ end_tac
QED

Theorem SPEC_Return_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc inst * evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ 2 ≤ LENGTH ss ∧ ISL e ∧
         offset = w2n (EL 0 ss) ∧ sz = w2n (EL 1 ss) ∧
         LENGTH caller.stack < stack_limit ∧
         (inst = Return ∨ inst = Revert) ∧
         returnCode = (inst = Return ∧ is_code_dest p.outputTo) ∧
         caller = FST (HD cs) ∧
         em = expanded_memory m offset sz ∧
         data = buffer_take offset sz em ∧
         gasCost = static_gas inst + memory_cost m offset sz + codeCost ∧
         all_pcs = (FDOM caller.msgParams.parsed ∪ FDOM p.parsed) ∧
         g + gasCost ≤ p.gasLimit ∧
         calleeGasLeft = p.gasLimit - g - gasCost ∧
         calleeGasLeft ≤ caller.gasUsed ∧
         (if returnCode then
          (case data of [] => T | h::_ => h ≠ 239w) ∧
          (codeCost = code_deposit_cost * LENGTH data) ∧
          (LENGTH data ≤ max_code_size) else codeCost = 0)))
  {}
  (evm_Stack ((case p.outputTo of
                 Code addr => (if inst = Return then w2w addr else b2w F)
               | _ => b2w (inst = Return))::caller.stack) *
   evm_Memory (case p.outputTo of Code _ => caller.memory | Memory r =>
               buffer_write r.offset (TAKE r.size data) caller.memory) *
   evm_PC (SUC caller.pc) *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData (if returnCode then [] else data) *
   evm_Exception (INL ()) *
   evm_Rollback (if returnCode then case p.outputTo of Code addr =>
                 rb with accounts updated_by (λaccounts.
                    update_account addr
                      (lookup_account addr accounts with code := data)
                      accounts) else if inst = Revert then cb else rb) *
   evm_GasUsed (caller.gasUsed - calleeGasLeft) *
   evm_JumpDest caller.jumpDest *
   evm_Logs (caller.logs ++ if inst = Revert then [] else l) *
   evm_AddRefund (caller.addRefund + if inst = Revert then 0 else ar) *
   evm_SubRefund (caller.subRefund + if inst = Revert then 0 else sr))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, STAR_CODE_POOL_evm2set,
                 EMPTY_evm2set, CODE_POOL_EMPTY, STAR_evm_hide_Parsed]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ qmatch_asmsub_abbrev_tac`_ < stack_limit ∧ is_ret ∧ _`
  \\ last_x_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ qpat_x_assum`is_ret`mp_tac
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ qpat_x_assum `SOME _ = _` $ assume_tac o SYM
  \\ strip_tac
  \\ `step_inst inst = step_return (inst = Return)`
     by gvs[Abbr`is_ret`, step_inst_def]
  \\ qpat_x_assum`is_ret`mp_tac
  \\ gvs [step_return_def,bind_def,ignore_bind_def,pop_stack_def,
          get_current_context_def,return_def,assert_def,
          set_current_context_def,memory_expansion_info_def,
          consume_gas_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ qmatch_asmsub_abbrev_tac`COND b1 (INL _)`
  \\ `b1` by (
       qpat_x_assum`g + _ ≤ _`mp_tac
       \\ simp[Abbr`b1`, memory_cost_def, EL_TAKE, HD_TAKE, Abbr`gasCost`]
       \\ rw[] )
  \\ gvs[expand_memory_def,bind_def,ignore_bind_def,get_current_context_def,
         return_def,set_current_context_def,read_memory_def,set_return_data_def]
  \\ strip_tac
  \\ `¬(SUC (LENGTH cs) ≤ 1)` by (Cases_on`cs` \\ gvs[])
  \\ `memory_expansion_cost (buffer_length m)
      (if 0 < sz then 32 * word_size (offset + sz) else 0) =
      memory_cost m offset sz` by gvs[memory_cost_def,memory_expand_by_def]
  \\ `p.gasLimit ≤ g + gasCost + caller.gasUsed`
     by gvs[Abbr`gasCost`,Abbr`calleeGasLeft`]
  \\ gs[EL_TAKE,HD_TAKE]
  \\ qmatch_asmsub_abbrev_tac`buffer_extend ex m`
  \\ `buffer_extend ex m = expanded_memory m offset sz` by
     gvs[expanded_memory_def, memory_expand_by_def]
  \\ gs[Abbr`ex`]
  \\ pop_assum kall_tac
  \\ Cases_on`inst = Revert`
  >- (
    gvs[revert_def, handle_step_def, handle_create_def, handle_def,
        return_destination_case_elim, reraise_def, bind_def, ignore_bind_def,
        get_return_data_def, get_current_context_def, return_def, get_output_to_def,
        handle_exception_def, get_num_contexts_def, pop_and_incorporate_context_def,
        get_gas_left_def, pop_context_def, unuse_gas_def, set_rollback_def,
        assert_def,set_current_context_def,inc_pc_def,return_destination_case_rator,
        CaseEq"return_destination",CaseEq"prod",CaseEq"sum",set_return_data_def,
        push_stack_def,write_memory_def,EMPTY_evm2set,SUBSET_DEF,PULL_EXISTS,
        Abbr`calleeGasLeft`,Abbr`all_pcs`,TO_FLOOKUP]
    \\ (conj_tac >- metis_tac[NOT_SOME_NONE])
    \\ (conj_tac >- metis_tac[NOT_SOME_NONE])
    \\ (conj_tac >-
         (qpat_x_assum ‘_ = {}’ mp_tac
          \\ fs [EXTENSION]
          \\ srw_tac[DNF_ss][TO_FLOOKUP]
          \\ eq_tac \\ rw []
          \\ first_x_assum(qspec_then`x`mp_tac)
          \\ simp[]
          \\ rw[] \\ metis_tac[option_CASES]))
    \\ irule UPDATE_evm2set_without
    \\ simp[]
    \\ gvs[TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
    \\ metis_tac[])
  \\ gvs[finish_def,handle_step_def,handle_create_def,handle_def,
         get_return_data_def,bind_def,ignore_bind_def,get_output_to_def,
         get_current_context_def,return_def]
  \\ Cases_on`p.outputTo`
  >- (
    gvs[reraise_def,handle_exception_def,bind_def,ignore_bind_def,get_num_contexts_def,
        pop_and_incorporate_context_def,get_return_data_def,get_output_to_def,
        inc_pc_def,set_return_data_def,push_stack_def,write_memory_def,return_def,
        get_current_context_def,set_current_context_def,get_gas_left_def,
        pop_context_def,unuse_gas_def,push_logs_def,update_gas_refund_def,
        assert_def,is_code_dest_def,SUBSET_DEF,PULL_EXISTS,EMPTY_evm2set,
        Abbr`calleeGasLeft`,Abbr`all_pcs`,TO_FLOOKUP]
    \\ (conj_tac >- metis_tac[NOT_SOME_NONE])
    \\ (conj_tac >- metis_tac[NOT_SOME_NONE])
    \\ (conj_tac >-
         (qpat_x_assum ‘_ = {}’ mp_tac
          \\ fs [EXTENSION]
          \\ srw_tac[DNF_ss][TO_FLOOKUP]
          \\ eq_tac \\ rw []
          \\ first_x_assum(qspec_then`x`mp_tac)
          \\ simp[]
          \\ rw[] \\ metis_tac[option_CASES]))
    \\ irule UPDATE_evm2set_without
    \\ simp[]
    \\ gvs[TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
    \\ metis_tac[]) \\
  gvs[reraise_def,handle_exception_def,bind_def,ignore_bind_def,get_num_contexts_def,
      pop_and_incorporate_context_def,get_return_data_def,get_output_to_def,
      inc_pc_def,set_return_data_def,push_stack_def,write_memory_def,return_def,
      get_current_context_def,set_current_context_def,get_gas_left_def,
      pop_context_def,unuse_gas_def,push_logs_def,update_gas_refund_def,
      assert_def,is_code_dest_def,SUBSET_DEF,PULL_EXISTS,EMPTY_evm2set,
      consume_gas_def,update_accounts_def,Abbr`all_pcs`,TO_FLOOKUP]
  \\ (conj_tac >- metis_tac[NOT_SOME_NONE])
  \\ (conj_tac >- metis_tac[NOT_SOME_NONE])
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {}’ mp_tac
        \\ fs [EXTENSION]
        \\ srw_tac[DNF_ss][TO_FLOOKUP]
        \\ eq_tac \\ rw []
        \\ first_x_assum(qspec_then`x`mp_tac)
        \\ simp[]
        \\ rw[] \\ metis_tac[option_CASES]))
  \\ irule UPDATE_evm2set_without
  \\ simp[]
  \\ gvs[TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem SPEC_Invalid_outermost:
  SPEC EVM_MODEL
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed g * evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ ISL e))
    {(pc,Invalid)}
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_GasUsed p.gasLimit * evm_ReturnData [] *
     evm_Exception (INR (SOME InvalidOpcode)))
Proof
  start_tac
  \\ gvs [step_inst_def,fail_def,bind_def,ignore_bind_def,
          handle_step_def,vfm_abort_def,handle_def,handle_create_def,
          get_return_data_def,get_output_to_def,reraise_def,
          handle_exception_def,get_gas_left_def,consume_gas_def,
          set_return_data_def,get_current_context_def,return_def,
          set_current_context_def,get_num_contexts_def,NULL_EQ,assert_def,
          return_destination_case_elim]
  \\ end_tac
QED

Theorem SPEC_Invalid_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc Invalid *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed)))
  {}
  (evm_Stack (b2w F::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Rollback cb *
   evm_GasUsed caller.gasUsed *
   evm_JumpDest caller.jumpDest *
   evm_Logs caller.logs *
   evm_AddRefund caller.addRefund *
   evm_SubRefund caller.subRefund)
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_EMPTY,
                  EMPTY_evm2set,STAR_evm_hide_Parsed, STAR_CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ qmatch_asmsub_abbrev_tac`_ < stack_limit ∧ is_ret ∧ _`
  \\ last_x_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ `¬(SUC (LENGTH (TL (SND r).contexts)) ≤ 1)` by (
       Cases_on`TL (SND r).contexts` \\ gvs[])
  \\ gvs[step_inst_def,fail_def,bind_def,ignore_bind_def,handle_step_def,
         vfm_abort_def,handle_def,handle_create_def,get_return_data_def,
         get_output_to_def,reraise_def,get_current_context_def,return_def,
         return_destination_case_rator]
  \\ qmatch_assum_rename_tac`wf_state r2`
  \\ `(FST (HD r2.contexts)).msgParams.parsed =
      parse_code 0 FEMPTY (FST (HD r2.contexts)).msgParams.code`
     by (gvs[wf_state_def] \\ Cases_on`r2.contexts` \\ gvs[wf_context_def])
  \\ `¬(SUC (LENGTH cs) ≤ 1)` by (Cases_on`cs` \\ gvs[])
  \\ Cases_on`p.outputTo`
  \\ gvs[CaseEq"prod",CaseEq"sum",handle_exception_def,get_num_contexts_def,
         inc_pc_def,pop_and_incorporate_context_def,push_stack_def,
         bind_def,ignore_bind_def,return_def,get_current_context_def,
         set_current_context_def,assert_def,get_return_data_def,
         get_output_to_def,set_return_data_def,get_gas_left_def,
         consume_gas_def,write_memory_def,pop_context_def,unuse_gas_def,
         set_rollback_def]
  \\ (rpt (conj_tac >- (
        gvs[Abbr`all_pcs`,TO_FLOOKUP,SUBSET_DEF, PULL_EXISTS] \\
        TRY (rpt strip_tac \\ drule FLOOKUP_parse_code_SOME_less_LENGTH
             \\ simp[] \\ NO_TAC)
        \\ metis_tac[NOT_SOME_NONE])))
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {}’ mp_tac
        \\ simp[EXTENSION,Abbr`all_pcs`] \\ rw [EQ_IMP_THM]
        \\ gvs[SUBSET_DEF,PULL_EXISTS]
        \\ last_x_assum(qspec_then`x`mp_tac)
        \\ simp[]
        \\ strip_tac \\ gvs[FORALL_PROD, TO_FLOOKUP]
        \\ metis_tac[option_CASES]))
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ ntac 2 strip_tac
  \\ gvs[SUBSET_DEF, PULL_EXISTS, TO_FLOOKUP, Abbr`all_pcs`]
  \\ qmatch_assum_rename_tac`HasParsed pc2 ∉ dom`
  \\ first_x_assum(qspec_then`pc2`mp_tac)
  \\ simp[]
  \\ strip_tac \\ gvs[]
QED

Theorem SPEC_Invalid: (* placeholder; see SPEC_Invalid_outermost and SPEC_Invalid_inner *)
  SPEC EVM_MODEL
  (evm_PC pc * cond F)
  {(pc,Invalid)}
  (evm_PC ARB)
Proof
  simp [SPEC_FALSE_PRE,SEP_CLAUSES]
QED

(*
  | Call precompile

open helperLib;

SPEC_COMPOSE_RULE [SPEC_Add,SPEC_Jump]

Example progression:
 1. subroutine that adds two given numbers
 2. code code that calls code of 1. (in a local way)
 3. verify an external call to 2.
 4. next level: external call as a transaction

val th = SPEC_Push |> Q.INST [‘n’|->‘1’,‘bs’|->‘[1w]’]
         |> SRULE [cv_transLib.cv_eval “word_of_bytes F (0w:bytes32) (REVERSE [1w])”]
val th = SPEC_COMPOSE_RULE [th,th,SPEC_Add] |> SRULE [EL,vfmOperationTheory.opcode_def];

val (th,goal_tm) = SPEC_WEAKEN_RULE th
  “evm_Stack (2w::ss) * evm_JumpDest j * evm_Exception e *
   evm_PC (pc + 5) * evm_GasUsed (g + 9) *
   evm_MsgParams p”

Triviality lemma:
  ^goal_tm
Proof
  cheat
QED

val th = MP th lemma

*)

Theorem SPEC_SelfDestruct_outermost:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_CachedRB cb * evm_ReturnData rd *
   evm_Exception e * evm_Rollback rb * evm_Msdomain d *
   cond (NULL cs ∧ ISL e ∧ ss ≠ [] ∧ ¬p.static ∧
         addr = w2w (HD ss) ∧ access_check d addr ∧
         sender = lookup_account p.callee rb.accounts ∧
         transferCost = (if 0 < sender.balance ∧
                            account_empty (lookup_account addr rb.accounts)
                         then self_destruct_new_account_cost else 0) ∧
         gasCost = static_gas SelfDestruct +
                   zero_warm (access_cost rb addr) + transferCost ∧
         g + gasCost ≤ p.gasLimit ∧
         rb1 = (accesses_add addr rb with accounts updated_by
                  transfer_value p.callee addr sender.balance) ∧
         rb2 = (if account_empty (lookup_account p.callee cb.accounts)
                then rb1 with <| accounts updated_by
                                   update_account p.callee
                                     (sender with balance := 0);
                                 toDelete updated_by CONS p.callee |>
                else rb1)))
  {(pc,SelfDestruct)}
  (evm_Stack (TL ss) * evm_PC pc * evm_GasUsed (g + gasCost) *
   evm_MsgParams p * evm_Contexts cs * evm_CachedRB cb *
   evm_ReturnData [] * evm_Exception (INR NONE) *
   evm_Msdomain (msdomain_add addr d) *
   evm_Rollback (case p.outputTo of Memory _ => rb2 | Code a =>
                 rb2 with accounts updated_by (λaccounts.
                    update_account a
                      (lookup_account a accounts with code := [])
                      accounts)))
Proof
  start_tac
  \\ Cases_on`(SND r).contexts` \\ gvs[NULL_EQ]
  \\ Cases_on`(FST h).stack` \\ gvs[]
  \\ gvs[step_inst_def,step_self_destruct_def,pop_stack_def,bind_def,
         ignore_bind_def,get_current_context_def,return_def,assert_def,
         set_current_context_def,access_address_split,get_callee_def,
         set_return_data_def,get_accounts_def,consume_gas_def,
         assert_not_static_def,get_static_def,update_accounts_def,
         get_original_def,add_to_delete_def,finish_def,HD_TAKE]
  \\ Cases_on`account_empty (lookup_account (FST h).msgParams.callee
                                             (SND h).accounts)`
  \\ Cases_on`(FST h).msgParams.outputTo`
  \\ gvs[bind_def,ignore_bind_def,return_def,update_accounts_def,
         add_to_delete_def,handle_step_def,vfm_abort_def,handle_def,
         handle_create_def,get_return_data_def,get_output_to_def,
         get_current_context_def,reraise_def,handle_exception_def,
         get_num_contexts_def,consume_gas_def,assert_def,
         set_current_context_def,CaseEq"prod",CaseEq"sum"]
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {_}’ $ rewrite_tac o single o GSYM
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []))
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on`h` \\ gvs[]
QED

Theorem SPEC_SelfDestruct_inner:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Contexts cs * evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
   evm_CachedRB cb * evm_Msdomain d *
   evm_Memory m * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_JumpDest j * evm_Parsed pc SelfDestruct *
   evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧ ISL e ∧
         caller = FST (HD cs) ∧
         all_pcs = (FDOM p.parsed ∪ FDOM caller.msgParams.parsed) ∧
         ss ≠ [] ∧ ¬p.static ∧
         addr = w2w (HD ss) ∧ access_check d addr ∧
         sender = lookup_account p.callee rb.accounts ∧
         transferCost = (if 0 < sender.balance ∧
                            account_empty (lookup_account addr rb.accounts)
                         then self_destruct_new_account_cost else 0) ∧
         gasCost = static_gas SelfDestruct +
                   zero_warm (access_cost rb addr) + transferCost ∧
         g + gasCost ≤ p.gasLimit ∧
         rb1 = (accesses_add addr rb with accounts updated_by
                  transfer_value p.callee addr sender.balance) ∧
         rb2 = (if account_empty
                     (lookup_account p.callee (SND (LAST cs)).accounts)
                then rb1 with <| accounts updated_by
                                   update_account p.callee
                                     (sender with balance := 0);
                                 toDelete updated_by CONS p.callee |>
                else rb1) ∧
         calleeGasLeft = p.gasLimit - (g + gasCost) ∧
         calleeGasLeft ≤ caller.gasUsed))
  {}
  (evm_Stack ((case p.outputTo of Code a => w2w a
                                | _ => 1w)::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   CODE_POOL EVM_INSTR {(pc,inst) |
                        FLOOKUP caller.msgParams.parsed pc = SOME inst} *
   evm_hide_Parsed (all_pcs DIFF FDOM caller.msgParams.parsed) *
   evm_Contexts (TL cs) *
   evm_CachedRB (SND (HD cs)) *
   evm_MsgParams (caller.msgParams) *
   evm_ReturnData [] *
   evm_Exception (INL ()) *
   evm_Msdomain (msdomain_add addr d) *
   evm_Rollback (case p.outputTo of Memory _ => rb2 | Code a =>
                 rb2 with accounts updated_by (λaccounts.
                    update_account a
                      (lookup_account a accounts with code := [])
                      accounts)) *
   evm_GasUsed (caller.gasUsed - calleeGasLeft) *
   evm_JumpDest caller.jumpDest *
   evm_Logs (caller.logs ++ l) *
   evm_AddRefund (caller.addRefund + ar) *
   evm_SubRefund (caller.subRefund + sr))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_EMPTY,
                  EMPTY_evm2set,STAR_evm_hide_Parsed, STAR_CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ qmatch_asmsub_abbrev_tac`_ < stack_limit ∧ is_ret ∧ _`
  \\ last_x_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on `ISR e` >- gvs[quantHeuristicsTheory.ISL_exists]
  \\ pop_assum (SUBST_ALL_TAC o EQF_INTRO)
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ `1 ≤ LENGTH ss` by (Cases_on`ss` \\ gvs[])
  \\ `¬(SUC (LENGTH cs) ≤ 1)` by (Cases_on`cs` \\ gvs[])
  \\ gvs[step_inst_def,step_self_destruct_def,pop_stack_def,bind_def,
         ignore_bind_def,get_current_context_def,return_def,assert_def,
         set_current_context_def,access_address_split,get_callee_def,
         set_return_data_def,get_accounts_def,consume_gas_def,
         assert_not_static_def,get_static_def,update_accounts_def,
         get_original_def,add_to_delete_def,finish_def,HD_TAKE,
         LAST_CONS_cond]
  \\ qmatch_assum_rename_tac`wf_state r2`
  \\ `(FST (HD r2.contexts)).msgParams.parsed =
      parse_code 0 FEMPTY (FST (HD r2.contexts)).msgParams.code`
     by (gvs[wf_state_def] \\ Cases_on`r2.contexts` \\ gvs[wf_context_def])
  \\ Cases_on`account_empty (lookup_account p.callee (SND (LAST cs)).accounts)`
  \\ Cases_on`p.outputTo`
  \\ gvs[CaseEq"prod",CaseEq"sum",bind_def,ignore_bind_def,return_def,
         update_accounts_def,add_to_delete_def,handle_step_def,vfm_abort_def,
         handle_def,handle_create_def,get_return_data_def,get_output_to_def,
         get_current_context_def,reraise_def,handle_exception_def,
         get_num_contexts_def,consume_gas_def,assert_def,
         set_current_context_def,inc_pc_def,pop_and_incorporate_context_def,
         push_stack_def,set_return_data_def,get_gas_left_def,
         write_memory_def,pop_context_def,unuse_gas_def,push_logs_def,
         update_gas_refund_def,Abbr`calleeGasLeft`]
  \\ (rpt (conj_tac >- (
        gvs[Abbr`all_pcs`,TO_FLOOKUP,SUBSET_DEF, PULL_EXISTS] \\
        TRY (rpt strip_tac \\ drule FLOOKUP_parse_code_SOME_less_LENGTH
             \\ simp[] \\ NO_TAC)
        \\ metis_tac[NOT_SOME_NONE])))
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {}’ mp_tac
        \\ simp[EXTENSION,Abbr`all_pcs`] \\ rw [EQ_IMP_THM]
        \\ gvs[SUBSET_DEF,PULL_EXISTS]
        \\ last_x_assum(qspec_then`x`mp_tac)
        \\ simp[]
        \\ strip_tac \\ gvs[FORALL_PROD, TO_FLOOKUP]
        \\ metis_tac[option_CASES]))
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ ntac 2 strip_tac
  \\ gvs[SUBSET_DEF, PULL_EXISTS, TO_FLOOKUP, Abbr`all_pcs`]
  \\ qmatch_assum_rename_tac`HasParsed pc2 ∉ dom`
  \\ first_x_assum(qspec_then`pc2`mp_tac)
  \\ simp[]
  \\ strip_tac \\ gvs[]
QED
