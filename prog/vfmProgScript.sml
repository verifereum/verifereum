Theory vfmProg
Ancestors
  vfmExecution vfmExecutionProp vfmContext vfmDecreasesGas
  prog words set_sep pred_set pair list
Libs
  wordsLib

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

(*
Theorem IN_evm2set[local]:
  (!r x s. aReg r x IN (evm2set s) ⇔ (x = V_READ_REG r s)) /\
  (!r x s. aReg r x IN (evm2set_on (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_REG r s) /\ r IN rs) /\
  (!r x s. aReg r x IN (evm2set_without (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_REG r s) /\ ~(r IN rs)) /\
  (!p x s. aMem p x IN (evm2set s) ⇔ (x = V_READ_MEM p s)) /\
  (!p x s. aMem p x IN (evm2set_on (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MEM p s) /\ p IN ms) /\
  (!p x s. aMem p x IN (evm2set_without (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MEM p s) /\ ~(p IN ms)) /\
  (!a x s. aStatus a x IN (evm2set s) ⇔ (x = V_READ_STATUS a s)) /\
  (!a x s. aStatus a x IN (evm2set_on (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_STATUS a s) /\ a IN st) /\
  (!a x s. aStatus a x IN (evm2set_without (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_STATUS a s) /\ ~(a IN st)) /\
  (!x s. aCPSR_Reg x IN (evm2set s) ⇔ (x = V_READ_MASKED_CPSR s)) /\
  (!x s. aCPSR_Reg x IN (evm2set_on (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MASKED_CPSR s) /\ cp) /\
  (!x s. aCPSR_Reg x IN (evm2set_without (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MASKED_CPSR s) /\ ~cp) /\
  (!x s. aUndef x IN (evm2set s) ⇔ (x = V_READ_UNDEF s)) /\
  (!x s. aUndef x IN (evm2set_on (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_UNDEF s) /\ ud) /\
  (!x s. aUndef x IN (evm2set_without (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_UNDEF s) /\ ~ud)
Proof
  cheat
  (*
  SRW_TAC [] [evm2set_on_def,evm2set_without_def,evm2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []); *)
QED
*)

Theorem evm2set_without_11[local]:
  !y y' s s'. (evm2set_without y' s' = evm2set_without y s) ==> (y = y')
Proof
  qsuff_tac`∀y y' s s'. evm2set_without y' s' ⊆ evm2set_without y s ⇒ y ⊆ y'`
  >- METIS_TAC[SET_EQ_SUBSET]
  \\ rw[evm2set_without_def, evm2set_def, SUBSET_DEF]
  \\ qpat_x_assum ‘!x. _’ mp_tac
  \\ simp[evm2set_on_def, PUSH_IN_INTO_IF]
  \\ srw_tac[DNF_ss][] (* TODO: faster? *)
  \\ CCONTR_TAC
  \\ Cases_on`x` \\ gvs[]
QED

(*
Theorem DELETE_evm2set[local]:
  (!a s. (evm2set_on (rs,ms,st,cp,ud) s) DELETE aReg a (V_READ_REG a s) =
         (evm2set_on (rs DELETE a,ms,st,cp,ud) s)) /\
  (!b s. (evm2set_on (rs,ms,st,cp,ud) s) DELETE aMem b (V_READ_MEM b s) =
         (evm2set_on (rs,ms DELETE b,st,cp,ud) s)) /\
  (!c s. (evm2set_on (rs,ms,st,cp,ud) s) DELETE aStatus c (V_READ_STATUS c s) =
         (evm2set_on (rs,ms,st DELETE c,cp,ud) s)) /\
  (!s. (evm2set_on (rs,ms,st,cp,ud) s) DELETE aCPSR_Reg (V_READ_MASKED_CPSR s) =
       (evm2set_on (rs,ms,st,F,ud) s)) /\
  (!s. (evm2set_on (rs,ms,st,cp,ud) s) DELETE aUndef (V_READ_UNDEF s) =
       (evm2set_on (rs,ms,st,cp,F) s))``
Proof
  SRW_TAC [] [evm2set_on_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []
QED
*)

Theorem EMPTY_evm2set[local]:
  (evm2set_on dom s = {}) ⇔  dom = {}
Proof
  simp[evm2set_on_def, PUSH_IN_INTO_IF, CaseEq"bool"]
  \\ rw[EXTENSION, EQ_IMP_THM]
  \\ Cases_on`x` \\ rw[]
QED

(*
val V_READ_MASKED_CPSR_THM =
 (SIMP_CONV std_ss [V_READ_MASKED_CPSR_def,encode_psr_def,word_slice_def] THENC
  ONCE_REWRITE_CONV [METIS_PROVE [] ``p /\ q ⇔ p /\ (p ==> q)``] THENC
  SIMP_CONV (std_ss++SIZES_ss) [
    fcpTheory.FCP_BETA,DECIDE “(i<=31⇔i<32:num)/\(i<=26⇔i<27)”] THENC
  ONCE_REWRITE_CONV [GSYM (METIS_PROVE [] ``p /\ q ⇔ p /\ (p ==> q)``)] THENC
  SIMP_CONV std_ss [DECIDE ``i<27 /\ i<32 ⇔ i<27``])
    ``V_READ_MASKED_CPSR s``
*)

(* ----------------------------------------------------------------------------- *)
(* Defining the V_MODEL                                                        *)
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

Definition evm_ReturnData_def:
  evm_ReturnData x = SEP_EQ { ReturnData x }
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
(* Theorems for construction of |- SPEC V_MODEL ...                            *)
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
  ((evm_Exception e * p) (evm2set_on dom s) ⇔
   (e = FST s) /\
   HasException ∈ dom /\ p (evm2set_on (dom DELETE HasException) s)) /\
  ((evm_Contexts c * p) (evm2set_on dom s) ⇔
   (c = TL (SND s).contexts) /\
   HasContexts ∈ dom /\ p (evm2set_on (dom DELETE HasContexts) s)) /\
  ((cond b * p) (evm2set_on dom s) ⇔
   b /\ p (evm2set_on dom s))
Proof
  simp [cond_STAR,EQ_STAR,
        evm_PC_def, evm_JumpDest_def, evm_MsgParams_def, evm_GasUsed_def,
        evm_ReturnData_def, evm_Stack_def, evm_Exception_def, evm_Contexts_def]
  \\ rw[EQ_IMP_THM]
  >>~- ([`_ ∈ _ (* g *)`] , gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  >>~- ([`_ = _ (* g *)`] , gvs[evm2set_on_def, PUSH_IN_INTO_IF])
  \\ qmatch_goalsub_abbrev_tac`p s1`
  \\ qmatch_asmsub_abbrev_tac`p s2`
  \\ `s1 = s2` suffices_by rw[]
  \\ rw[Abbr`s1`, Abbr`s2`]
  \\ gvs[evm2set_on_def, EXTENSION, PUSH_IN_INTO_IF]
  \\ rw[EQ_IMP_THM]
QED

val CODE_POOL_evm2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) ⇔ (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

(*
val CODE_POOL_evm2set_2 = prove(
  ``CODE_POOL V_INSTR {(p,c);(q,d)} (evm2set_on (rs,ms,st,cp,ud) s) ⇔
      ({p+3w;p+2w;p+1w;p;q+3w;q+2w;q+1w;q} = ms) /\ (rs = {}) /\ (st = {}) /\ ~cp /\ ~ud /\
      (V_READ_MEM (p + 0w) s = ( 7 ><  0) c) /\
      (V_READ_MEM (p + 1w) s = (15 ><  8) c) /\
      (V_READ_MEM (p + 2w) s = (23 >< 16) c) /\
      (V_READ_MEM (p + 3w) s = (31 >< 24) c) /\
      (V_READ_MEM (q + 0w) s = ( 7 ><  0) d) /\
      (V_READ_MEM (q + 1w) s = (15 ><  8) d) /\
      (V_READ_MEM (q + 2w) s = (23 >< 16) d) /\
      (V_READ_MEM (q + 3w) s = (31 >< 24) d)``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,V_INSTR_def,CODE_POOL_evm2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_evm2set,INSERT_UNION_EQ]
  \\ Cases_on `(31 >< 24) c = V_READ_MEM (p + 3w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(23 >< 16) c = V_READ_MEM (p + 2w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(15 ><  8) c = V_READ_MEM (p + 1w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `( 7 ><  0) c = V_READ_MEM (p + 0w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(31 >< 24) d = V_READ_MEM (q + 3w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(23 >< 16) d = V_READ_MEM (q + 2w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(15 ><  8) d = V_READ_MEM (q + 1w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `( 7 ><  0) d = V_READ_MEM (q + 0w) s` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [DELETE_evm2set,EMPTY_evm2set,DIFF_INSERT]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC,DIFF_EMPTY,EMPTY_evm2set]);
*)

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
    first_assum(qspec_then`Parsed p (SOME c) T`mp_tac)
    \\ simp_tac (srw_ss()) []
    \\ strip_tac
    \\ Cases \\ simp[] \\ CCONTR_TAC \\ gvs[]
    \\ fsrw_tac[DNF_ss][EQ_IMP_THM] (* TODO: faster? *)
    \\ metis_tac[] )
  \\ Cases \\ simp[]
  \\ rw[EQ_IMP_THM]
QED

(*
val V_WRITE_STS_def = Define `
  V_WRITE_STS a x s = if a IN {psrN;psrZ;psrC;psrV;psrQ} then V_WRITE_STATUS a x s else s`;

val V_WRITE_STS_INTRO = store_thm("V_WRITE_STS_INTRO",
  ``(V_WRITE_STATUS psrN x s = V_WRITE_STS psrN x s) /\
    (V_WRITE_STATUS psrZ x s = V_WRITE_STS psrZ x s) /\
    (V_WRITE_STATUS psrC x s = V_WRITE_STS psrC x s) /\
    (V_WRITE_STATUS psrV x s = V_WRITE_STS psrV x s) /\
    (V_WRITE_STATUS psrQ x s = V_WRITE_STS psrQ x s)``,
  SIMP_TAC std_ss [V_WRITE_STS_def,IN_INSERT]);

val UNDEF_OF_UPDATES = prove(
  ``(!a x. V_READ_UNDEF (V_WRITE_REG a x s) = V_READ_UNDEF s) /\
    (!a x. V_READ_UNDEF (V_WRITE_MEM a x s) = V_READ_UNDEF s) /\
    (!a x. V_READ_UNDEF (V_WRITE_STS a x s) = V_READ_UNDEF s) /\
    (!a x. V_READ_UNDEF (V_WRITE_MEM_WRITE a x s) = V_READ_UNDEF s) /\
    (!a. V_READ_UNDEF (V_WRITE_MEM_READ a s) = V_READ_UNDEF s) /\
    (!a x y. V_READ_UNDEF (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = V_READ_UNDEF s)``,
  SIMP_TAC std_ss [V_READ_UNDEF_def,V_OK_def] \\ REPEAT STRIP_TAC
  \\ EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC);

val MASKED_CPSR_OF_UPDATES = prove(
  ``(!a x. V_READ_MASKED_CPSR (V_WRITE_STS a x s) = V_READ_MASKED_CPSR s) /\
    (!a x. V_READ_MASKED_CPSR (V_WRITE_REG a x s) = V_READ_MASKED_CPSR s) /\
    (!a x. V_READ_MASKED_CPSR (V_WRITE_MEM a x s) = V_READ_MASKED_CPSR s) /\
    (!a x. V_READ_MASKED_CPSR (V_WRITE_MEM_WRITE a x s) = V_READ_MASKED_CPSR s) /\
    (!a. V_READ_MASKED_CPSR (V_WRITE_MEM_READ a s) = V_READ_MASKED_CPSR s) /\
    (!a x y. V_READ_MASKED_CPSR (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = V_READ_MASKED_CPSR s)``,
  SIMP_TAC std_ss [V_READ_MASKED_CPSR_THM,V_OK_def] \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC std_ss [V_WRITE_STS_def]
    \\ Cases_on `a IN {psrN; psrZ; psrC; psrV; psrQ}` \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
    \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,NOT_IN_EMPTY] \\ EVAL_TAC)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC \\ EVAL_TAC);

val V_READ_WRITE = LIST_CONJ [REG_OF_UPDATES,MEM_OF_UPDATES,MASKED_CPSR_OF_UPDATES,
                                UNDEF_OF_UPDATES,CPSR_COMPONENTS_OF_UPDATES]
val _ = save_thm("V_READ_WRITE",V_READ_WRITE);

val V_OK_WRITE_GE = prove(
  ``V_OK (V_WRITE_GE w4 s) = V_OK s``,
  SIMP_TAC std_ss [V_OK_def] \\ EVAL_TAC);

val UPDATE_evm2set_without_GE = prove(
  ``(!w4. evm2set_without (rs,ms,st,cp,ud) (V_WRITE_GE w4 s) = evm2set_without (rs,ms,st,cp,ud) s)``,
  SIMP_TAC std_ss [evm2set_def,evm2set_without_def,evm2set_on_def,REG_OF_UPDATES,
    MEM_OF_UPDATES,V_READ_WRITE,V_READ_UNDEF_def,V_OK_WRITE_GE]

val UPDATE_evm2set_without = store_thm("UPDATE_evm2set_without",
  ``(!a x. a IN rs ==> (evm2set_without (rs,ms,st,cp,ud) (V_WRITE_REG a x s) = evm2set_without (rs,ms,st,cp,ud) s)) /\
    (!a x. a IN ms ==> (evm2set_without (rs,ms,st,cp,ud) (V_WRITE_MEM a x s) = evm2set_without (rs,ms,st,cp,ud) s)) /\
    (!b x. b IN st ==> (evm2set_without (rs,ms,st,cp,ud) (V_WRITE_STS b x s) = evm2set_without (rs,ms,st,cp,ud) s)) /\
    (!a x. evm2set_without (rs,ms,st,cp,ud) (V_WRITE_MEM_WRITE a x s) = evm2set_without (rs,ms,st,cp,ud) s) /\
    (!a. evm2set_without (rs,ms,st,cp,ud) (V_WRITE_MEM_READ a s) = evm2set_without (rs,ms,st,cp,ud) s) /\
    (!x y. evm2set_without (rs,ms,st,cp,ud) (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = evm2set_without (rs,ms,st,cp,ud) s)``,
  SIMP_TAC std_ss [evm2set_def,evm2set_without_def,evm2set_on_def,EXTENSION,IN_UNION,
    IN_IMAGE,IN_DIFF,IN_UNIV,NOT_IN_EMPTY,IN_INSERT,V_READ_WRITE,PUSH_IN_INTO_IF]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `xx = yy` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ FULL_SIMP_TAC std_ss [v_el_distinct,v_el_11]
  \\ IMP_RES_TAC (METIS_PROVE [] ``x IN s /\ ~(y IN s) ==> ~(x = y:'a)``)
  \\ ASM_SIMP_TAC std_ss [V_READ_WRITE,UNDEF_OF_UPDATES]
  \\ SIMP_TAC std_ss [V_WRITE_STS_def] \\ TRY (Cases_on `b IN {psrN; psrZ; psrC; psrV; psrQ}`)
  \\ FULL_SIMP_TAC std_ss [V_READ_WRITE,UNDEF_OF_UPDATES]
  \\ METIS_TAC []);
*)

Theorem UPDATE_evm2set_without[local]:
  wf_state s ∧
  ctxt = FST (HD s.contexts) ∧
  rb = SND (HD s.contexts) ∧
  s' = s with contexts := (ctxt', rb)::TL s.contexts ∧
  ctxt'.msgParams.parsed = ctxt.msgParams.parsed ∧
  ctxt'.msgParams.code = ctxt.msgParams.code ∧
  s' = SND r' ∧ s = SND r ∧
  wf_state s' ∧
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
  (HasPC ∉ dom ⇒ ctxt'.pc = ctxt.pc)
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

val binop_tac =
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
  \\ gvs [step_inst_def,step_binop_def,step_modop_def,pop_stack_def,bind_def,
          ignore_bind_def,get_current_context_def,return_def,assert_def,
          set_current_context_def,consume_gas_def,push_stack_def,
          inc_pc_or_jump_def,is_call_def,with_zero_mod_def,step_monop_def,
          step_pop_def,step_exp_def,exp_cost_def,exponent_byte_size_def]
  \\ Cases_on ‘(FST (HD (SND r).contexts)).stack’ \\ gvs[]
  \\ Cases_on ‘FST r’ \\ gvs[]
  \\ TRY(qmatch_goalsub_rename_tac`HD (TAKE _ hs)` \\ Cases_on`hs` \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`DROP _ hs` \\ Cases_on`hs` \\ gvs[])
  \\ TRY(qmatch_goalsub_rename_tac`HD (TAKE _ hs)` \\ Cases_on`hs` \\ gvs[])
  \\ conj_tac
  >-
   (qpat_x_assum ‘_ = {_}’ $ rewrite_tac o single o GSYM
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [])
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ qmatch_goalsub_rename_tac ‘p = (_,_)’
  \\ Cases_on ‘p’ \\ gvs[]

Theorem SPEC_Stop_tx:
  SPEC EVM_MODEL
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_ReturnData rd * evm_Exception e *
     cond (NULL cs ∧ (∃m. p.outputTo = Memory m)))
    {(pc,Stop)}
    (evm_PC pc * evm_MsgParams p * evm_Contexts cs *
     evm_ReturnData [] * evm_Exception (INR NONE))
Proof
  irule IMP_EVM_SPEC \\ rpt strip_tac
  \\ simp [STAR_evm2set, GSYM STAR_ASSOC, CODE_POOL_evm2set]
  \\ qmatch_goalsub_abbrev_tac ‘b ⇒ _’
  \\ Cases_on ‘b’ \\ fs []
  \\ drule step_preserves_wf_state
  \\ qmatch_assum_rename_tac ‘wf_state (SND r)’
  \\ Cases_on ‘step (SND r)’ \\ fs []
  \\ strip_tac
  \\ ‘(SND r).contexts ≠ []’ by fs [wf_state_def]
  \\ gvs [step_def,handle_def,bind_def,get_current_context_def,
          return_def, SF CONJ_ss]
  \\ gvs [step_inst_def,bind_def,ignore_bind_def,set_return_data_def,
          get_current_context_def,return_def,set_current_context_def,
          finish_def,handle_step_def,handle_def,handle_create_def,
          get_return_data_def,get_output_to_def,handle_exception_def,
          reraise_def,get_num_contexts_def,NULL_EQ]
  \\ irule UPDATE_evm2set_without
  \\ simp[execution_state_component_equality]
  \\ Cases_on ‘(SND r).contexts’ \\ gvs[]
  \\ qmatch_goalsub_rename_tac ‘p = (_,_)’
  \\ Cases_on ‘p’ \\ gvs[]
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
