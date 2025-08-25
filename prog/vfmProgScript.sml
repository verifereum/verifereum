Theory vfmProg
Ancestors
  vfmExecution vfmExecutionProp
  prog words set_sep pred_set pair
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
         | Parsed     num (opname option)
         | Contexts   ((context # rollback_state) list)  (* other contexts *)
         | TxParams   transaction_parameters
         | Rollback   rollback_state
         | Msdomain   domain_mode
End

Type evm_set = “:evm_el set”;

(*-------------------------------------------------------------------------------*
   Converting from execution_state record to v_set
 *-------------------------------------------------------------------------------*)

Definition EVM_READ_UNDEF_def:
  EVM_READ_UNDEF s = ~(wf_state s)
End

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
          | HasContexts
          | HasTxParams
          | HasRollback
          | HasMsdomain
End

Definition evm2set'_def:
  evm2set' dom (s:execution_state) =
    let current_context = FST (HD s.contexts) in
      (if HasStack ∈ dom      then { Stack (current_context.stack) } else {}) ∪
      (if HasMemory ∈ dom     then { Memory (current_context.memory) } else {}) ∪
      (if HasPC ∈ dom         then { PC (current_context.pc) } else {}) ∪
      (if HasJumpDest ∈ dom   then { JumpDest (current_context.jumpDest) } else {}) ∪
      (if HasReturnData ∈ dom then { ReturnData (current_context.returnData) } else {}) ∪
      (if HasGasUsed ∈ dom    then { GasUsed (current_context.gasUsed) } else {}) ∪
      (if HasAddRefund ∈ dom  then { AddRefund (current_context.addRefund) } else {}) ∪
      (if HasSubRefund ∈ dom  then { SubRefund (current_context.subRefund) } else {}) ∪
      (if HasLogs ∈ dom       then { Logs (current_context.logs) } else {}) ∪
      (if HasContexts ∈ dom   then { Contexts (TL s.contexts) } else {}) ∪
      (if HasTxParams ∈ dom   then { TxParams s.txParams } else {}) ∪
      (if HasRollback ∈ dom   then { Rollback s.rollback } else {}) ∪
      (if HasMsdomain ∈ dom   then { Msdomain s.msdomain } else {}) ∪
      { Parsed n (FLOOKUP current_context.msgParams.parsed n) | HasParsed n ∈ dom }
End

Definition evm2set_def:
  evm2set s = evm2set' UNIV s
End

Definition evm2set''_def:
  evm2set'' x s = evm2set s DIFF evm2set' x s
End

(* theorems *)

Theorem PUSH_IN_INTO_IF[local]:
  !g x y z. x IN (if g then y else z) <=> if g then x IN y else x IN z
Proof
  metis_tac[]
QED

Theorem evm2set'_SUBSET_evm2set[local]:
  ∀y s. evm2set' y s SUBSET evm2set s
Proof
  rw[evm2set_def]
  \\ simp[SUBSET_DEF, IN_UNIV, evm2set'_def, PUSH_IN_INTO_IF]
  \\ rw[]
QED

Theorem SPLIT_evm2set[local]:
  ∀x s. SPLIT (evm2set s) (evm2set' x s, evm2set'' x s)
Proof
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,evm2set''_def]
  \\ `evm2set' x s SUBSET evm2set s` by METIS_TAC [evm2set'_SUBSET_evm2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]
QED

Theorem SUBSET_evm2set[local]:
  !u s. u SUBSET evm2set s <=> ?y. u = evm2set' y s
Proof
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [evm2set'_SUBSET_evm2set]
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
       (if ∃x. Logs x ∈ u then {HasLogs} else {}) ∪
       (if ∃x. Contexts x ∈ u then {HasContexts} else {}) ∪
       (if ∃x. TxParams x ∈ u then {HasTxParams} else {}) ∪
       (if ∃x. Rollback x ∈ u then {HasRollback} else {}) ∪
       (if ∃x. Msdomain x ∈ u then {HasMsdomain} else {}) ∪
       {HasParsed n | ∃x. Parsed n x ∈ u}`
  \\ rewrite_tac[EXTENSION, EQ_IMP_THM]
  \\ gen_tac \\ strip_tac
  >- (
    strip_tac \\ first_x_assum drule
    \\ simp[evm2set'_def, PUSH_IN_INTO_IF]
    \\ rw[] \\ goal_assum $ drule )
  \\ simp[evm2set'_def, PUSH_IN_INTO_IF]
  \\ strip_tac
  \\ first_x_assum drule
  \\ rw[evm2set'_def] \\ rw[]
QED

Theorem SPLIT_evm2set_EXISTS[local]:
  ∀s u v. SPLIT (evm2set s) (u,v) = ?y. (u = evm2set' y s) /\ (v = evm2set'' y s)
Proof
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_evm2set]
  \\ gvs[SPLIT_def]
  \\ `u SUBSET (evm2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ gvs[evm2set''_def, SUBSET_evm2set]
  \\ qexists_tac`y` \\ simp[]
  \\ gvs[EXTENSION, IN_DISJOINT]
  \\ metis_tac[]
QED

(*
Theorem IN_evm2set[local]:
  (!r x s. aReg r x IN (evm2set s) ⇔ (x = V_READ_REG r s)) /\
  (!r x s. aReg r x IN (evm2set' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_REG r s) /\ r IN rs) /\
  (!r x s. aReg r x IN (evm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_REG r s) /\ ~(r IN rs)) /\
  (!p x s. aMem p x IN (evm2set s) ⇔ (x = V_READ_MEM p s)) /\
  (!p x s. aMem p x IN (evm2set' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MEM p s) /\ p IN ms) /\
  (!p x s. aMem p x IN (evm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MEM p s) /\ ~(p IN ms)) /\
  (!a x s. aStatus a x IN (evm2set s) ⇔ (x = V_READ_STATUS a s)) /\
  (!a x s. aStatus a x IN (evm2set' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_STATUS a s) /\ a IN st) /\
  (!a x s. aStatus a x IN (evm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_STATUS a s) /\ ~(a IN st)) /\
  (!x s. aCPSR_Reg x IN (evm2set s) ⇔ (x = V_READ_MASKED_CPSR s)) /\
  (!x s. aCPSR_Reg x IN (evm2set' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MASKED_CPSR s) /\ cp) /\
  (!x s. aCPSR_Reg x IN (evm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_MASKED_CPSR s) /\ ~cp) /\
  (!x s. aUndef x IN (evm2set s) ⇔ (x = V_READ_UNDEF s)) /\
  (!x s. aUndef x IN (evm2set' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_UNDEF s) /\ ud) /\
  (!x s. aUndef x IN (evm2set'' (rs,ms,st,cp,ud) s) ⇔ (x = V_READ_UNDEF s) /\ ~ud)
Proof
  cheat
  (*
  SRW_TAC [] [evm2set'_def,evm2set''_def,evm2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []); *)
QED
*)

Theorem evm2set''_11[local]:
  !y y' s s'. (evm2set'' y' s' = evm2set'' y s) ==> (y = y')
Proof
  cheat (*
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st cp ud. y = (r,m,st,cp,ud)` by METIS_TAC [PAIR]
  \\ `?r' m' st' cp' ud'. y' = (r',m',st',cp',ud')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ, Excl "lift_disj_eq"] THENL [
    `?a. ~(a IN r ⇔ a IN r')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. aReg a x IN evm2set'' y s) = (?x. aReg a x IN evm2set'' y' s'))`,
    `?a. ~(a IN m ⇔ a IN m')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. aMem a x IN evm2set'' y s) = (?x. aMem a x IN evm2set'' y' s'))`,
    `?a. ~(a IN st ⇔ a IN st')` by METIS_TAC [EXTENSION]
    \\ sg `~((?x. aStatus a x IN evm2set'' y s) = (?x. aStatus a x IN evm2set'' y' s'))`,
    sg `~((?x. aCPSR_Reg x IN evm2set'' y s) = (?x. aCPSR_Reg x IN evm2set'' y' s'))`,
    sg `~((?x. aUndef x IN evm2set'' y s) = (?x. aUndef x IN evm2set'' y' s'))`]
  \\ REPEAT (FULL_SIMP_TAC bool_ss [IN_evm2set] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `evm2set'' _ _ = evm2set'' _ _` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [IN_evm2set] \\ METIS_TAC [] *)
QED

(*
Theorem DELETE_evm2set[local]:
  (!a s. (evm2set' (rs,ms,st,cp,ud) s) DELETE aReg a (V_READ_REG a s) =
         (evm2set' (rs DELETE a,ms,st,cp,ud) s)) /\
  (!b s. (evm2set' (rs,ms,st,cp,ud) s) DELETE aMem b (V_READ_MEM b s) =
         (evm2set' (rs,ms DELETE b,st,cp,ud) s)) /\
  (!c s. (evm2set' (rs,ms,st,cp,ud) s) DELETE aStatus c (V_READ_STATUS c s) =
         (evm2set' (rs,ms,st DELETE c,cp,ud) s)) /\
  (!s. (evm2set' (rs,ms,st,cp,ud) s) DELETE aCPSR_Reg (V_READ_MASKED_CPSR s) =
       (evm2set' (rs,ms,st,F,ud) s)) /\
  (!s. (evm2set' (rs,ms,st,cp,ud) s) DELETE aUndef (V_READ_UNDEF s) =
       (evm2set' (rs,ms,st,cp,F) s))``
Proof
  SRW_TAC [] [evm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []
QED
*)

Theorem EMPTY_evm2set[local]:
  (evm2set' dom s = {}) ⇔  dom = {}
Proof
  cheat
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

Definition evm_PC_def:
  evm_PC s = SEP_EQ { PC s }
End

Definition EVM_NEXT_REL_def:
  EVM_NEXT_REL s s' = (step s = (INL (), s'))
End

Definition EVM_INSTR_def:
  EVM_INSTR (n,op) = { Parsed n (SOME op) }
End

Definition EVM_MODEL_def:
  EVM_MODEL = (evm2set, EVM_NEXT_REL, EVM_INSTR,
               (λx y. x = (y:execution_state)),
               (K F):execution_state -> bool)
End

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_evm2set]
  ``p (evm2set' y s) ==> (?u v. SPLIT (evm2set s) (u,v) /\ p u /\ (\v. v = evm2set'' y s) v)``;

Theorem EVM_SPEC_SEMANTICS:
  SPEC EVM_MODEL p {} q =
  ∀y s seq. p (evm2set' y s) /\ rel_sequence EVM_NEXT_REL seq s ==>
            ∃k. q (evm2set' y (seq k)) /\ (evm2set'' y s = evm2set'' y (seq k))
Proof
  SIMP_TAC std_ss [GSYM RUN_EQ_SPEC,RUN_def,EVM_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_evm2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = evm2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_evm2set_EXISTS]
  \\ IMP_RES_TAC evm2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []
QED


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC V_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

Theorem STAR_evm2set:
  ((evm_PC n * p) (evm2set' dom s) ⇔
   (n = (FST (HD s.contexts)).pc) /\ HasPC ∈ dom /\ p (evm2set' (dom DELETE HasPC) s)) /\
  ((cond g * p) (evm2set' dom s) ⇔
   g /\ p (evm2set' dom s))
Proof
  simp [evm_PC_def,cond_STAR,EQ_STAR]
  \\ cheat
QED

val CODE_POOL_evm2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) ⇔ (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

(*
val CODE_POOL_evm2set_2 = prove(
  ``CODE_POOL V_INSTR {(p,c);(q,d)} (evm2set' (rs,ms,st,cp,ud) s) ⇔
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
  CODE_POOL EVM_INSTR {(p,c)} (evm2set' dom s) ⇔
    dom = {HasParsed p} ∧
    FLOOKUP (FST (HD s.contexts)).msgParams.parsed n = SOME c
Proof
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,EVM_INSTR_def,CODE_POOL_evm2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET]
  \\ cheat (*
evm2set'_def
IN_evm2set
  \\ Cases_on `(31 >< 24) c = V_READ_MEM (p + 3w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(23 >< 16) c = V_READ_MEM (p + 2w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(15 ><  8) c = V_READ_MEM (p + 1w) s` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `( 7 ><  0) c = V_READ_MEM (p + 0w) s` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [DELETE_evm2set,EMPTY_evm2set,DIFF_INSERT]
  \\ ASM_SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC,DIFF_EMPTY,EMPTY_evm2set]); *)
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

val UPDATE_evm2set''_GE = prove(
  ``(!w4. evm2set'' (rs,ms,st,cp,ud) (V_WRITE_GE w4 s) = evm2set'' (rs,ms,st,cp,ud) s)``,
  SIMP_TAC std_ss [evm2set_def,evm2set''_def,evm2set'_def,REG_OF_UPDATES,
    MEM_OF_UPDATES,V_READ_WRITE,V_READ_UNDEF_def,V_OK_WRITE_GE]

val UPDATE_evm2set'' = store_thm("UPDATE_evm2set''",
  ``(!a x. a IN rs ==> (evm2set'' (rs,ms,st,cp,ud) (V_WRITE_REG a x s) = evm2set'' (rs,ms,st,cp,ud) s)) /\
    (!a x. a IN ms ==> (evm2set'' (rs,ms,st,cp,ud) (V_WRITE_MEM a x s) = evm2set'' (rs,ms,st,cp,ud) s)) /\
    (!b x. b IN st ==> (evm2set'' (rs,ms,st,cp,ud) (V_WRITE_STS b x s) = evm2set'' (rs,ms,st,cp,ud) s)) /\
    (!a x. evm2set'' (rs,ms,st,cp,ud) (V_WRITE_MEM_WRITE a x s) = evm2set'' (rs,ms,st,cp,ud) s) /\
    (!a. evm2set'' (rs,ms,st,cp,ud) (V_WRITE_MEM_READ a s) = evm2set'' (rs,ms,st,cp,ud) s) /\
    (!x y. evm2set'' (rs,ms,st,cp,ud) (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) =
           evm2set'' (rs,ms,st,cp,ud) s)``,
  SIMP_TAC std_ss [evm2set_def,evm2set''_def,evm2set'_def,EXTENSION,IN_UNION,
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

val V_SPEC_CODE =
  SPEC_CODE |> ISPEC ``EVM_MODEL``
  |> SIMP_RULE std_ss [EVM_MODEL_def]
  |> REWRITE_RULE [GSYM EVM_MODEL_def];

Theorem IMP_EVM_SPEC_LEMMA[local]:
  ∀p q.
    (∀s dom.
       ∃s'.
         (p (evm2set' dom s) ==>
          (step s = (INL (), s')) /\ q (evm2set' dom s') /\
          (evm2set'' dom s = evm2set'' dom s'))) ==>
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
