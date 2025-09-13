Theory vfmProg
Ancestors
  vfmExecution vfmExecutionProp vfmContext vfmConstants vfmDecreasesGas
  prog words set_sep pred_set pair list arithmetic finite_map
Libs
  wordsLib intLib

(*-------------------------------------------------------------------------------*
   State set
 *-------------------------------------------------------------------------------*)

Datatype:
  evm_el = Stack      (bytes32 list)                     (* from top context *)
         | Memory     (byte list)
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
                 (n < LENGTH current_context.msgParams.code ∧ wf_state s)
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
QED

Theorem EMPTY_evm2set[local]:
  (evm2set_on dom s = {}) ⇔  dom = {}
Proof
  simp[evm2set_on_def, PUSH_IN_INTO_IF, CaseEq"bool"]
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
    ∃fx fy. s = BIGUNION $ IMAGE (λpc. { Parsed pc (fx pc) (fy pc) }) pcs)
End

Definition EVM_NEXT_REL_def:
  EVM_NEXT_REL (s: unit execution_result) s' = (step (SND s) = s')
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
  ((evm_Memory rd * p) (evm2set_on dom s) ⇔
   (rd = (FST (HD (SND s).contexts)).memory) /\
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
    pc < LENGTH (FST (HD (SND s).contexts)).msgParams.code ∧ HasParsed pc IN dom ∧
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
    \\ strip_tac \\ gvs[])
  \\ first_assum $ irule_at Any
  \\ simp[SPLIT_def]
  \\ simp[evm2set_on_def, PUSH_IN_INTO_IF, Once EXTENSION, PULL_EXISTS]
  \\ gvs[SF DNF_ss, Once EQ_IMP_THM, SUBSET_DEF]
  \\ qmatch_goalsub_abbrev_tac`_ _ = fx _`
  \\ qmatch_goalsub_abbrev_tac`_ < len`
  \\ qexistsl_tac[`λpc. pc < len ∧ wf_state (SND s)`,`fx`]
  \\ simp[]
QED

Theorem STAR_SEP_HIDE_evm_JumpDest:
  (~evm_JumpDest * p) (evm2set_on dom s) <=>
  HasJumpDest IN dom ∧ p (evm2set_on (dom DELETE HasJumpDest) s)
Proof
  rw[evm_JumpDest_def, SEP_HIDE_def, SEP_EXISTS_THM, STAR_def, PULL_EXISTS, SEP_EQ_def]
  \\ rw[EQ_IMP_THM]
  >- (
    gvs[SPLIT_def]
    \\ `JumpDest x IN evm2set_on dom s` by (gvs[EXTENSION] \\ metis_tac[])
    \\ gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  >- (
    gvs[SPLIT_def]
    \\ qmatch_goalsub_abbrev_tac`p s1`
    \\ qmatch_asmsub_abbrev_tac`p s2`
    \\ `s1 = s2` suffices_by rw[]
    \\ rw[Abbr`s1`, Abbr`s2`]
    \\ gvs[evm2set_on_def, EXTENSION, PUSH_IN_INTO_IF]
    \\ rw[EQ_IMP_THM]
    \\ fsrw_tac[DNF_ss][EQ_IMP_THM]
    \\ last_x_assum drule \\ rw[]
    \\ gvs[])
  \\ first_assum $ irule_at Any
  \\ simp[SPLIT_def]
  \\ simp[evm2set_on_def, PUSH_IN_INTO_IF, EXTENSION]
  \\ gvs[SF DNF_ss, EQ_IMP_THM]
QED

val CODE_POOL_evm2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) ⇔ (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

Theorem CODE_POOL_evm2set:
  CODE_POOL EVM_INSTR {(p,c)} (evm2set_on dom s) ⇔
    dom = {HasParsed p} ∧
    FLOOKUP (FST (HD (SND s).contexts)).msgParams.parsed p = SOME c ∧
    p < LENGTH (FST (HD (SND s).contexts)).msgParams.code ∧
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
        ((pc < LENGTH ctxt'.msgParams.code <=> pc < LENGTH ctxt.msgParams.code) ∧
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
          (step (SND s) = s') /\ q (evm2set_on dom s') /\
          (evm2set_without dom s = evm2set_without dom s'))) ==>
    SPEC EVM_MODEL p {} q
Proof
  SIMP_TAC std_ss [RIGHT_EXISTS_IMP_THM] \\ REWRITE_TAC [EVM_SPEC_SEMANTICS]
  \\ SIMP_TAC std_ss [FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,EVM_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0`
  \\ first_x_assum $ qspec_then ‘0’ mp_tac
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem IMP_EVM_SPEC =
  (ONCE_REWRITE_RULE [STAR_COMM] o REWRITE_RULE [V_SPEC_CODE] o
   SPECL [``CODE_POOL EVM_INSTR c * p'``,
          ``CODE_POOL EVM_INSTR c * q'``]) IMP_EVM_SPEC_LEMMA;

(*-------------------------------------------------------------------------------*
   Hoare triples for specific opcodes
 *-------------------------------------------------------------------------------*)

(* TODO: move? *)
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

Definition accesses_add_slot_def:
  accesses_add_slot sk rb =
  rb with accesses updated_by
  (λx. x with storageKeys updated_by fINSERT sk)
End

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
  memory_cost (m: word8 list) offset size =
  memory_expansion_cost (LENGTH m)
    (if 0 < size then word_size (offset + size) * 32 else 0)
End

Definition memory_expand_by_def:
  memory_expand_by (m: word8 list) offset size =
  MAX (LENGTH m) (if 0 < size then word_size (offset + size) * 32 else 0)
  - (LENGTH m)
End

Definition expanded_memory_def:
  expanded_memory (m: word8 list) offset size =
  m ++ REPLICATE (memory_expand_by m offset size) 0w
End

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
  TAKE offset em ++ TAKE sz (DROP sourceOffset em) ++
  DROP (offset + sz) (em:word8 list)
End

Theorem return_destination_case_rator[local] =
  DatatypeSimps.mk_case_rator_thm_tyinfo $ Option.valOf $
  TypeBase.read {Thy="vfmContext", Tyop="return_destination"}

val start_tac =
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ simp [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ Cases_on ‘b’ \\ fs []
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
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
          get_return_data_check_def,get_return_data_def,
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
         \\ conj_tac
         >- (
           simp[MCopy_write_def]
           \\ qmatch_goalsub_abbrev_tac`DROP _ ls`
           \\ rewrite_tac[LENGTH_TAKE_EQ]
           \\ IF_CASES_TAC >- rw[]
           \\ Q.SUBGOAL_THEN `xOffset + xSize ≤ LENGTH ls` assume_tac
           >- (
             simp[Abbr`ls`, word_size_def, MAX_DEF]
             \\ rw[]
             >- COOPER_TAC
             \\ pop_assum mp_tac \\ rw[]
             >- COOPER_TAC
             \\ gvs[max_expansion_range_def]
             \\ Cases_on `HD t = 0w` \\ gvs[]
             \\ qpat_x_assum`_ = (_,_)`mp_tac
             \\ rw[])
           \\ qpat_x_assum`_ = (_,_)`mp_tac
           \\ rw[max_expansion_range_def]
           \\ pop_assum mp_tac \\ rw[]
           \\ gvs[]))
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {_}’ $ rewrite_tac o single o GSYM
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []))
  \\ end_tac

Theorem SPEC_Stop_outermost:
  SPEC EVM_MODEL
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_ReturnData rd * evm_Exception e * evm_Rollback rb *
     cond (NULL cs))
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
   ~evm_JumpDest * evm_Parsed pc Stop * evm_hide_Parsed (all_pcs DELETE pc) *
   cond (cs ≠ [] ∧ LENGTH caller.stack < stack_limit ∧
         caller = FST (HD cs) ∧
         all_pcs = (count (LENGTH caller.msgParams.code) ∪
                    count (LENGTH p.code) ∪
                    FDOM caller.msgParams.parsed ∪
                    FDOM p.parsed) ∧
         calleeGasLeft = p.gasLimit - g ∧
         calleeGasLeft ≤ caller.gasUsed))
  {}
  (evm_Stack ((case p.outputTo of Code addr => w2w addr
                                        | _ => 1w)::caller.stack) *
   evm_Memory (caller.memory) *
   evm_PC (SUC caller.pc) *
   evm_hide_Parsed all_pcs *
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
   ~evm_JumpDest *
   evm_Logs (caller.logs ++ l) *
   evm_AddRefund (caller.addRefund + ar) *
   evm_SubRefund (caller.subRefund + sr))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ simp [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_def,
           EMPTY_evm2set,STAR_evm_hide_Parsed,STAR_SEP_HIDE_evm_JumpDest]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ Cases_on ‘b’ \\ fs []
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
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
         return_destination_case_rator,consume_gas_def,update_accounts_def,
         CaseEq"prod",CaseEq"sum",CaseEq"return_destination",
         handle_exception_def,get_num_contexts_def,inc_pc_def,
         pop_and_incorporate_context_def,push_stack_def,
         write_memory_def,pop_context_def,unuse_gas_def,push_logs_def,
         update_gas_refund_def,get_gas_left_def]
  \\ (rpt (conj_tac >- (gvs[SUBSET_DEF, PULL_EXISTS] \\ metis_tac[])))
  \\ (conj_tac >-
       (qpat_x_assum ‘_ = {}’ mp_tac
        \\ simp[EXTENSION] \\ rw [EQ_IMP_THM]
        \\ metis_tac[]))
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ ntac 2 strip_tac
  \\ gvs[SUBSET_DEF, PULL_EXISTS, TO_FLOOKUP]
  \\ metis_tac[]
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
    (evm_Stack (w2w (get_byte (EL 0 ss) (EL 1 ss) T) :: DROP 2 ss) *
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
               TAKE sz (DROP offset em)) :: DROP 2 ss) *
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
              DROP (w2n (HD ss)) p.data) :: TL ss) *
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
  (evm_Stack (n2w (LENGTH p.data) :: ss) *
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
   evm_Memory (TAKE offset em ++
               take_pad_0 sz (DROP (w2n (EL 1 ss)) p.data) ++
               DROP (offset + sz) em) *
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
   evm_Memory (TAKE offset em ++
               take_pad_0 sz (DROP (w2n (EL 1 ss)) p.code) ++
               DROP (offset + sz) em) *
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
   evm_Memory (TAKE offset em ++
               take_pad_0 sz (DROP (w2n (EL 2 ss))
                 (lookup_account a rb.accounts).code) ++
               DROP (offset + sz) em) *
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
   evm_Memory (TAKE offset em ++
               take_pad_0 sz (DROP sourceOffset rd) ++
               DROP (offset + sz) em) *
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
  (evm_Stack (word_of_bytes F 0w (REVERSE (TAKE 32 (DROP offset em)))
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
   evm_Memory (TAKE offset em ++ bytes ++ DROP (offset + LENGTH bytes) em) *
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
   evm_Memory (TAKE offset em ++ bytes ++ DROP (offset + LENGTH bytes) em) *
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
   evm_AddRefund ar * evm_SubRefund sr * evm_Contexts cs *
   cond (2 ≤ LENGTH ss ∧ j = NONE ∧ ISL e ∧
         key = HD ss ∧ value = EL 1 ss ∧
         ~p.static ∧ call_stipend < p.gasLimit - g ∧
         sk = SK p.callee key ∧ access_slot_check d sk ∧ cs ≠ [] ∧
         (cost,ad,sd) =
           SStore_gas (SND (LAST cs)).accounts rb p.callee key value ∧
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
    (evm_Stack (n2w (LENGTH m) :: ss) *
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
                data := TAKE sz (DROP offset em)|> ∧
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
   cond (3 ≤ LENGTH ss ∧
         value = w2n (EL 0 ss) ∧ offset = w2n (EL 1 ss) ∧ sz = w2n (EL 2 ss) ∧
         em = expanded_memory m offset sz ∧
         gas = static_gas Create + init_code_word_cost * (word_size sz) +
               memory_cost m offset sz ∧
         code = TAKE sz (DROP offset em) ∧
         sender = lookup_account p.callee rb.accounts ∧
         addr = address_for_create p.callee sender.nonce ∧
         access_check d addr ∧
         LENGTH code ≤ 2 * max_code_size ∧
         gasLeft = p.gasLimit - g - gas ∧
         cappedGas = gasLeft - gasLeft DIV 64 ∧
         ¬p.static ∧
         (sender.balance < value ∨ SUC sender.nonce ≥ 2 ** 64 ∨
          SUC (LENGTH cs) > 1024) ∧
         access_storage_check d addr ∧
         g + gas + cappedGas ≤ p.gasLimit))
  {(pc,Create)}
  (evm_Stack (b2w F :: DROP 3 ss) * evm_PC (SUC pc) *
   evm_GasUsed (g + gas) * evm_MsgParams p *
   evm_Exception (INL ()) * evm_ReturnData [] *
   evm_Rollback (accesses_add addr rb) * evm_Memory em * evm_Contexts cs *
   evm_Msdomain (msdomain_add_storage addr $ msdomain_add addr d))
Proof
  qmatch_goalsub_abbrev_tac`~_ ∧ djs ∧ _`
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
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ qpat_x_assum`djs`mp_tac
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ gvs[step_inst_def, step_create_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split]
  \\ qmatch_asmsub_abbrev_tac`COND (LENGTH code1 ≤ 2 * _)`
  \\ `code1 = code` by simp[Abbr`code1`, Abbr`code`, Abbr`em`,
                            expanded_memory_def, memory_expand_by_def]
  \\ gvs[Abbr`code1`]
  \\ gvs[bind_def, ignore_bind_def, return_def,
         get_current_context_def, get_gas_left_def]
  \\ gvs[assert_not_static_def, get_static_def, bind_def, ignore_bind_def,
         assert_def, return_def, get_current_context_def, set_return_data_def,
         set_current_context_def, get_num_contexts_def, access_storage_split, HD_TAKE]
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ gvs[abort_unuse_def, unuse_gas_def, bind_def, ignore_bind_def,
         return_def, fail_def, assert_def, get_current_context_def,
         set_current_context_def, push_stack_def, inc_pc_def,
         inc_pc_or_jump_def, is_call_def]
  \\ conj_tac >- simp[expanded_memory_def, memory_expand_by_def, Abbr`em`]
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
   cond (3 ≤ LENGTH ss ∧
         value = w2n (EL 0 ss) ∧ offset = w2n (EL 1 ss) ∧ sz = w2n (EL 2 ss) ∧
         em = expanded_memory m offset sz ∧
         gas = static_gas Create + init_code_word_cost * (word_size sz) +
               memory_cost m offset sz ∧
         code = TAKE sz (DROP offset em) ∧
         sender = lookup_account p.callee rb.accounts ∧
         addr = address_for_create p.callee sender.nonce ∧
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
  {(pc,Create)}
  (evm_Stack (b2w F :: DROP 3 ss) * evm_PC (SUC pc) *
   evm_GasUsed (g + gas + cappedGas) * evm_MsgParams p *
   evm_Exception (INL ()) * evm_ReturnData [] *
   evm_Rollback (accesses_add addr rb
                 with accounts updated_by increment_nonce p.callee) *
   evm_Memory em * evm_Contexts cs *
   evm_Msdomain (msdomain_add_storage addr $ msdomain_add addr d))
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
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ gvs[step_inst_def, step_create_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split]
  \\ qmatch_asmsub_abbrev_tac`COND (LENGTH code1 ≤ 2 * _)`
  \\ `code1 = code` by simp[Abbr`code1`, Abbr`code`, Abbr`em`,
                            expanded_memory_def, memory_expand_by_def]
  \\ gvs[Abbr`code1`]
  \\ gvs[bind_def, ignore_bind_def, return_def,
         get_current_context_def, get_gas_left_def]
  \\ gvs[assert_not_static_def, get_static_def, bind_def, ignore_bind_def,
         assert_def, return_def, get_current_context_def, set_return_data_def,
         set_current_context_def, get_num_contexts_def, access_storage_split, HD_TAKE,
         abort_create_exists_def, update_accounts_def,
         fail_def, assert_def, get_current_context_def,
         set_current_context_def, push_stack_def, inc_pc_def,
         inc_pc_or_jump_def, is_call_def]
  \\ conj_tac >- simp[expanded_memory_def, memory_expand_by_def, Abbr`em`]
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
   evm_Parsed pc Create * evm_hide_Parsed (all_pcs DELETE pc) *
   cond (3 ≤ LENGTH ss ∧
         value = w2n (EL 0 ss) ∧ offset = w2n (EL 1 ss) ∧ sz = w2n (EL 2 ss) ∧
         em = expanded_memory m offset sz ∧
         gas = static_gas Create + init_code_word_cost * (word_size sz) +
               memory_cost m offset sz ∧
         code = TAKE sz (DROP offset em) ∧
         sender = lookup_account p.callee rb.accounts ∧
         addr = address_for_create p.callee sender.nonce ∧
         access_check d addr ∧
         LENGTH code ≤ 2 * max_code_size ∧
         gasLeft = p.gasLimit - g - gas ∧
         cappedGas = gasLeft - gasLeft DIV 64 ∧
         ¬p.static ∧
         value ≤ sender.balance ∧ SUC sender.nonce < 2 ** 64 ∧
         SUC (LENGTH cs) ≤ 1024 ∧
         ¬account_already_created (lookup_account addr rb.accounts) ∧
         access_storage_check d addr ∧
         all_pcs = count (LENGTH p.code) ∪ FDOM p.parsed ∪
                   count (LENGTH code) ∪ FDOM (parse_code 0 FEMPTY code) ∧
         g + gas + cappedGas ≤ p.gasLimit ∧
         tx = <|from := p.callee; to := SOME addr; value := value;
                gasLimit := cappedGas; data := []; nonce := 0; gasPrice := 0;
                accessList := []; blobVersionedHashes := [];
                maxFeePerGas := NONE; maxFeePerBlobGas := NONE|> ∧
         (orig_rb = if NULL cs then cb else SND (LAST cs)) ∧
         orig = update_account addr empty_account_state orig_rb.accounts ∧
         caller = <|stack := DROP 3 ss; memory := em; pc := pc; jumpDest := j;
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
   evm_Memory [] *
   evm_AddRefund 0 * evm_SubRefund 0 * evm_Logs [] *
   evm_hide_Parsed all_pcs *
   evm_Contexts (set_last_accounts orig $ (caller, cb) :: cs) *
   evm_CachedRB caller_rb *
   evm_Msdomain (msdomain_add_storage addr $ msdomain_add addr d))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, STAR_evm_hide_Parsed, CODE_POOL_def]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ ‘wf_context (FST (HD (SND r).contexts))’ by (
    Cases_on ‘(SND r).contexts’ \\ gvs[wf_state_def] )
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, wf_context_def, SF CONJ_ss]
  \\ gvs[step_inst_def, step_create_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split]
  \\ qmatch_asmsub_abbrev_tac`COND (LENGTH code1 ≤ 2 * _)`
  \\ `code1 = code` by simp[Abbr`code1`, Abbr`code`, Abbr`em`,
                            expanded_memory_def, memory_expand_by_def]
  \\ gvs[Abbr`code1`]
  \\ gvs[bind_def, ignore_bind_def, return_def,
         get_current_context_def, get_gas_left_def]
  \\ gvs[assert_not_static_def, get_static_def, bind_def, ignore_bind_def,
         assert_def, return_def, get_current_context_def, set_return_data_def,
         set_current_context_def, get_num_contexts_def, access_storage_split, HD_TAKE,
         proceed_create_def, update_accounts_def, get_rollback_def, get_original_def,
         set_original_def, push_context_def, inc_pc_or_jump_def, is_call_def]
  \\ conj_tac >- (gvs[SUBSET_DEF, PULL_EXISTS] \\ metis_tac[])
  \\ conj_tac >- (
       simp[Abbr`orig`, Abbr`caller_rb`, Abbr`caller`, Abbr`orig_rb`,
            LAST_CONS_cond, NULL_EQ, Abbr`cb`]
       \\ qmatch_goalsub_abbrev_tac`_ a1 _ = _ a2 _`
       \\ `a1 = a2` by (rw[Abbr`a1`, Abbr`a2`,Abbr`rb`] \\ gvs[])
       \\ simp[] \\ AP_TERM_TAC \\ simp[]
       \\ simp[context_component_equality]
       \\ simp[Abbr`em`,expanded_memory_def,memory_expand_by_def])
  \\ gs[EMPTY_evm2set]
  \\ conj_tac >-
      (qpat_x_assum ‘_ = {}’ mp_tac
       \\ fs [EXTENSION, Abbr`all_pcs`]
       \\ srw_tac[DNF_ss][TO_FLOOKUP]
       \\ eq_tac \\ rw []
       \\ first_x_assum(qspec_then`x`mp_tac)
       \\ simp[]
       \\ rw[])
  \\ irule UPDATE_evm2set_without
  \\ simp[]
  \\ gvs[Abbr`all_pcs`,TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
  \\ simp[initial_msg_params_def]
  \\ metis_tac[]
QED

Theorem SPEC_Call_fail_balance:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e *
   cond (7 ≤ LENGTH ss ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧ value = w2n (EL 2 ss) ∧
         argsOffset = w2n (EL 3 ss) ∧ argsSize = w2n (EL 4 ss) ∧
         retOffset = w2n (EL 5 ss) ∧ retSize = w2n (EL 6 ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         access_check d addr ∧
         toAccount = lookup_account addr rb.accounts ∧
         cCost = (if call_inst = Call ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + call_value_cost + cCost) = (dynamicGas, stipend) ∧
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
   evm_Rollback (accesses_add addr rb) *
   evm_Msdomain (msdomain_add addr d) *
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
  \\ gvs[step_call_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, get_gas_left_def, HD_TAKE,
         assert_not_static_def, get_static_def, abort_call_value_def, push_stack_def,
         set_return_data_def, unuse_gas_def, inc_pc_def, inc_pc_or_jump_def]
  \\ conj_tac >- simp[Abbr`em`, expanded_memory_def, memory_expand_by_def]
  \\ conj_tac >-
       (qpat_x_assum ‘{_} = _’ $ rewrite_tac o single
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ end_tac
QED

Theorem SPEC_Call_fail_depth:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e * evm_Contexts cs *
   cond (6 + vOff ≤ LENGTH ss ∧ vOff = (if call_has_value call_inst then 1 else 0) ∧
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
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost) = (dynamicGas, stipend) ∧
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
   evm_Rollback (accesses_add addr rb) *
   evm_Msdomain (msdomain_add addr d) *
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
         access_address_split, get_gas_left_def, HD_TAKE]
  \\ qmatch_asmsub_abbrev_tac`(COND a b c) (s1:execution_state)`
  \\ Q.SUBGOAL_THEN `(COND a b c) s1 = (INL (), s1)` assume_tac
  >- rw[Abbr`a`,Abbr`b`,Abbr`c`,return_def,assert_not_static_def,
        bind_def, ignore_bind_def, get_static_def, assert_def,
        get_current_context_def,Abbr`s1`]
  \\ gvs[Abbr`s1`,bind_def,ignore_bind_def,set_return_data_def,get_current_context_def,
         return_def,set_current_context_def,get_num_contexts_def,abort_unuse_def,
         unuse_gas_def,assert_def, push_stack_def, inc_pc_def, inc_pc_or_jump_def,
         Abbr`c`]
  \\ conj_tac >- simp[Abbr`em`, expanded_memory_def, memory_expand_by_def]
  \\ conj_tac >-
       (qpat_x_assum ‘{_} = _’ $ rewrite_tac o single
        \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ end_tac
QED

Theorem SPEC_Call:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_JumpDest j * evm_Exception e * evm_CachedRB cb * evm_Contexts cs *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_Parsed pc call_inst * evm_hide_Parsed (all_pcs DELETE pc) *
   cond (6 + vOff ≤ LENGTH ss ∧ vOff = (if call_has_value call_inst then 1 else 0) ∧
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
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost) = (dynamicGas, stipend) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         sender = lookup_account p.callee rb.accounts ∧
         value ≤ sender.balance ∧
         LENGTH cs < 1024 ∧
         data = TAKE (argsSize) (DROP argsOffset em) ∧
         callee = (if call_inst = CallCode ∨ call_inst = DelegateCall
                   then p.callee else addr) ∧
         tx = <|from := if call_inst = DelegateCall then p.caller else p.callee;
                to := SOME callee;
                value := if call_inst = DelegateCall then p.value else value;
                gasLimit := stipend; data := data; nonce := 0; gasPrice := 0;
                accessList := []; blobVersionedHashes := [];
                maxFeePerGas := NONE; maxFeePerBlobGas := NONE|> ∧
         ¬fIN addr precompile_addresses ∧
         all_pcs = count (LENGTH p.code) ∪ FDOM p.parsed ∪
                   count (LENGTH toAccount.code) ∪
                   FDOM (parse_code 0 FEMPTY toAccount.code) ∧
         caller = <|stack := DROP (6 + vOff) ss; memory := em; pc := pc; jumpDest := j;
                    returnData := []; gasUsed := g + gasCost; addRefund := ar;
                    subRefund := sr; logs := l; msgParams := p|>))
  {}
  (evm_Stack [] * evm_PC 0 * evm_GasUsed 0 *
   evm_MsgParams (initial_msg_params callee toAccount.code
                  (call_inst = StaticCall ∨ p.static)
                  (Memory <|offset := retOffset; size := retSize|>) tx) *
   evm_Memory [] *
   evm_AddRefund 0 * evm_SubRefund 0 * evm_Logs [] *
   evm_JumpDest NONE *
   evm_hide_Parsed all_pcs *
   evm_Contexts ((caller,cb) :: cs) *
   evm_CachedRB (accesses_add addr rb) *
   evm_Rollback (accesses_add addr rb with accounts updated_by
                 (if call_inst ≠ CallCode ∧ 0 < value
                  then transfer_value p.callee addr value
                  else I)) *
   evm_Msdomain (msdomain_add addr d) *
   evm_Exception (INL ()) *
   evm_ReturnData [])
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ rewrite_tac[STAR_evm2set, GSYM STAR_ASSOC, STAR_evm_hide_Parsed, CODE_POOL_def]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ reverse $ Cases_on ‘b’ >- simp[]
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  \\ rpt (qpat_x_assum`_ = _`(assume_tac o
                              ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ gvs[]
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
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
  \\ `g + dynamicGas + mCost + static_gas call_inst ≤ p.gasLimit` by gvs[Abbr`gasCost`]
  \\ gvs[step_call_def, bind_def, return_def, ignore_bind_def,
         pop_stack_def, get_current_context_def, assert_def, set_current_context_def,
         memory_expansion_info_def, consume_gas_def, expand_memory_def, EL_TAKE,
         memory_cost_def, read_memory_def, get_callee_def, get_accounts_def,
         access_address_split, HD_TAKE, get_gas_left_def]
  \\ qpat_x_assum`step_inst _ = _`kall_tac
  \\ qmatch_asmsub_abbrev_tac`(COND a b c) (s1:execution_state)`
  \\ Q.SUBGOAL_THEN `(COND a b c) s1 = (INL (), s1)` assume_tac
  >- rw[Abbr`a`,Abbr`b`,Abbr`c`,return_def,assert_not_static_def,
        bind_def, ignore_bind_def, get_static_def, assert_def,
        get_current_context_def,Abbr`s1`]
  \\ gvs[Abbr`s1`,bind_def,ignore_bind_def,set_return_data_def,get_current_context_def,
         return_def,set_current_context_def,get_num_contexts_def,abort_unuse_def,
         unuse_gas_def,assert_def, push_stack_def, inc_pc_def, inc_pc_or_jump_def,
         Abbr`c`,proceed_call_def,get_rollback_def,read_memory_def]
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
  \\ conj_tac >- gvs[Abbr`em`, expanded_memory_def, memory_expand_by_def]
  \\ gvs[SUBSET_DEF, PULL_EXISTS]
  \\ conj_tac >- metis_tac[]
  \\ conj_tac >-
       simp[Abbr`caller`,Abbr`em`, expanded_memory_def, memory_expand_by_def,
            context_component_equality,Abbr`gasCost`]
  \\ gvs[EMPTY_evm2set]
  \\ conj_tac >-
      (qpat_x_assum ‘_ = {}’ mp_tac
       \\ fs [EXTENSION, Abbr`all_pcs`]
       \\ srw_tac[DNF_ss][TO_FLOOKUP]
       \\ eq_tac \\ rw []
       \\ first_x_assum(qspec_then`x`mp_tac)
       \\ simp[]
       \\ rw[])
  \\ irule UPDATE_evm2set_without
  \\ simp[]
  \\ gvs[Abbr`all_pcs`,TO_FLOOKUP,Once EXTENSION,SUBSET_DEF,PULL_EXISTS]
  \\ simp[initial_msg_params_def]
  \\ metis_tac[]
QED

(*
  | Call precompile
  | Return
  | Create2
  | Revert
  | Invalid
  | SelfDestruct
*)
