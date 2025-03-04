open HolKernel boolLib bossLib Parse BasicProvers
     pairTheory finite_setTheory pred_setTheory
     vfmExecutionTheory
     vfmContextTheory vfmDomainSeparationTheory;

val () = new_theory "vfmDomainCollection";

(* TODO: move *)

Theorem IN_toSet_fINSERT:
  x ∈ toSet (fINSERT a s) ⇔ x = a ∨ x ∈ toSet s
Proof
  rw[GSYM fIN_IN]
QED

(* -- *)

Definition computes_minimal_domain_def:
  computes_minimal_domain m =
  ∀s r t d. m s = (r, t) ∧ s.msdomain = Collect d ⇒
  (* no outside domain errors when collecting *)
  (∀x. r ≠ INR (SOME (OutsideDomain x))) ∧
  (* collection always produces the same result and an extended domain *)
  (∀d'. ∃d''.
     m (s with msdomain := Collect d') =
     (r, t with msdomain := Collect d'') ∧
     subdomain d' d'') ∧
  (* the result of collection is enforceable *)
  (∀d' d''. t.msdomain = Collect d' ∧ subdomain d' d'' ⇒
     m (s with msdomain := Enforce d'') =
     (r, t with msdomain := Enforce d'')) ∧
  (* anything less than collection fails, i.e. it is minimal *)
  (∀d' d''. t.msdomain = Collect d' ∧ subdomain d d'' ∧ ¬subdomain d' d'' ⇒
           ∃x s'. m (s with msdomain := Enforce d'') =
                 (INR (SOME (OutsideDomain x)), s'))
End

Theorem fail_computes_minimal_domain[simp]:
  (∀x. e ≠ OutsideDomain x) ⇒
  computes_minimal_domain (fail e)
Proof
  rw[computes_minimal_domain_def, fail_def]
  \\ qexists_tac`d'` \\ simp[]
QED

Theorem return_computes_minimal_domain[simp]:
  computes_minimal_domain (return x)
Proof
  rw[computes_minimal_domain_def, return_def]
  \\ qexists_tac`d'` \\ simp[]
QED

Theorem get_current_context_computes_minimal_domain[simp]:
  computes_minimal_domain get_current_context
Proof
  rw[computes_minimal_domain_def, get_current_context_def]
  \\ rpt (pop_assum mp_tac)
  \\ rw[return_def, fail_def]
  \\ qexists_tac`d'` \\ rw[]
QED

Theorem with_same_msdomain[simp]:
  d = s.msdomain ⇒
  (s with msdomain := d) = s
Proof
  rw[execution_state_component_equality]
QED

Theorem eq_with_msdomain[simp]:
  (s = s with msdomain := d) ⇔
  s.msdomain = d
Proof
  rw[execution_state_component_equality]
QED

Theorem bind_computes_minimal_domain:
  computes_minimal_domain f ∧ (∀x. computes_minimal_domain (g x))
  ⇒
  computes_minimal_domain (bind f g)
Proof
  rw[bind_def, computes_minimal_domain_def, CaseEq"prod"]
  >- (
    Cases_on`v` \\ gvs[]
    \\ first_x_assum(drule_then drule) \\ rw[]
    \\ last_x_assum(qspec_then`d`mp_tac)
    \\ simp[] \\ strip_tac
    \\ first_x_assum(drule_then drule) \\ rw[]
    \\ first_x_assum(drule_then drule) \\ rw[] )
  >- (
    first_x_assum(drule_then drule) \\ rw[]
    \\ last_assum(qspec_then`d'`mp_tac)
    \\ strip_tac \\ gvs[]
    \\ reverse TOP_CASE_TAC \\ gvs[]
    >- rw[execution_state_component_equality]
    \\ first_x_assum(qspec_then`d`mp_tac)
    \\ rw[]
    \\ last_x_assum(drule_then drule) \\ rw[]
    \\ first_x_assum(qspec_then`d''`(fn th =>
         strip_assume_tac th \\ CHANGED_TAC(simp[])))
    \\ rw[execution_state_component_equality]
    \\ metis_tac[subdomain_trans] )
  >- (
    first_x_assum(drule_then drule) \\ strip_tac
    \\ last_assum(qspec_then`d`mp_tac)
    \\ strip_tac \\ gvs[]
    \\ Cases_on`v` \\ gvs[]
    \\ first_x_assum(drule_then drule) \\ strip_tac
    \\ qmatch_asmsub_rename_tac`s'.msdomain = Collect d1`
    \\ qpat_assum(`∀d. ∃d'. _`)(qspec_then`d1`strip_assume_tac)
    \\ gvs[]
    \\ `subdomain d1 d''` by metis_tac[subdomain_trans]
    \\ first_x_assum (drule_then(fn th =>
         strip_assume_tac th \\ CHANGED_TAC(simp[]))) )
  \\ first_x_assum(drule_then drule) \\ strip_tac
  \\ reverse (Cases_on`v`) \\ gvs[]
  >- ( first_x_assum (drule_then drule) \\ rw[] \\ rw[] )
  \\ first_assum(qspec_then`d`(qx_choose_then`d1`strip_assume_tac))
  \\ gvs[]
  \\ first_x_assum(drule_then drule) \\ strip_tac
  \\ reverse(Cases_on`subdomain d1 d''`)
  >- ( first_x_assum(drule_then drule) \\ rw[] \\ rw[] )
  \\ first_x_assum (drule_then (fn th =>
       strip_assume_tac th \\ CHANGED_TAC(simp[])))
QED

Theorem ignore_bind_computes_minimal_domain:
  computes_minimal_domain f ∧
  computes_minimal_domain g
  ⇒
  computes_minimal_domain (ignore_bind f g)
Proof
  rw[ignore_bind_def]
  \\ irule bind_computes_minimal_domain
  \\ rw[]
QED

Theorem handle_computes_minimal_domain:
  computes_minimal_domain f ∧
  (∀s t x. f s = (INR (SOME (OutsideDomain x)), t) ⇒
           FST $ g (SOME (OutsideDomain x)) t = INR (SOME (OutsideDomain x))) ∧
  (∀e. (∀x. e ≠ SOME (OutsideDomain x)) ⇒ computes_minimal_domain (g e))
  ⇒
  computes_minimal_domain (handle f g)
Proof
  rw[handle_def, computes_minimal_domain_def, CaseEq"prod"]
  >- (
    first_x_assum(drule_then drule) \\ rw[]
    \\ Cases_on`v2` \\ gvs[]
    \\ first_x_assum(qspec_then`d`(CHOOSE_THEN strip_assume_tac))
    \\ gvs[]
    \\ first_x_assum(drule_then drule) \\ rw[] )
  >- (
    first_x_assum(drule_then drule) \\ rw[]
    \\ first_assum(qspec_then`d'`(qx_choose_then`d1`strip_assume_tac))
    \\ gvs[]
    \\ TOP_CASE_TAC \\ gvs[]
    >- rw[execution_state_component_equality]
    \\ first_assum(qspec_then`d`(qx_choose_then`d2`strip_assume_tac))
    \\ gvs[]
    \\ first_x_assum(drule_then drule) \\ rw[]
    \\ first_x_assum(qspec_then`d1`(qx_choose_then`d3`strip_assume_tac))
    \\ rw[execution_state_component_equality]
    \\ metis_tac[subdomain_trans] )
  >- (
    first_x_assum(drule_then drule) \\ rw[]
    \\ first_assum(qspec_then`d`(CHOOSE_THEN strip_assume_tac))
    \\ gvs[]
    \\ Cases_on`v2` \\ gvs[]
    \\ first_x_assum(drule_then drule) \\ rw[]
    \\ qmatch_asmsub_rename_tac`s'.msdomain = Collect d1`
    \\ qpat_assum(`∀d. ∃d'. _`)(qspec_then`d1`strip_assume_tac)
    \\ gvs[]
    \\ `subdomain d1 d''` by metis_tac[subdomain_trans]
    \\ first_x_assum (drule_then(fn th =>
         strip_assume_tac th \\ CHANGED_TAC(simp[]))) )
  \\ first_x_assum(drule_then drule) \\ strip_tac
  \\ (Cases_on`v2`) \\ gvs[]
  >- ( first_x_assum (drule_then drule) \\ rw[] \\ rw[]
       \\ first_x_assum drule \\ metis_tac[PAIR])
  \\ first_assum(qspec_then`d`(qx_choose_then`d1`strip_assume_tac))
  \\ gvs[]
  \\ first_x_assum(drule_then drule) \\ strip_tac
  \\ reverse(Cases_on`subdomain d1 d''`)
  >- ( first_x_assum(drule_then drule) \\ rw[] \\ rw[]
       \\ first_x_assum drule \\ metis_tac[PAIR])
  \\ first_x_assum (drule_then (fn th =>
       strip_assume_tac th \\ CHANGED_TAC(simp[])))
QED

Theorem reraise_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (reraise e)
Proof
  rw[reraise_def, computes_minimal_domain_def]
  \\ rw[execution_state_component_equality]
QED

val return_destination_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vfmContext",Tyop="return_destination"}));

val option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

Theorem get_gas_left_computes_minimal_domain[simp]:
  computes_minimal_domain get_gas_left
Proof
  rw[get_gas_left_def]
  \\ irule bind_computes_minimal_domain
  \\ rw[]
QED

Theorem assert_computes_minimal_domain[simp]:
  (¬b ⇒ ∀x. e ≠ (OutsideDomain x)) ⇒
  computes_minimal_domain (assert b e)
Proof
  rw[assert_def, computes_minimal_domain_def]
  \\ rw[execution_state_component_equality]
QED

Theorem set_current_context_computes_minimal_domain[simp]:
  computes_minimal_domain (set_current_context x)
Proof
  rw[set_current_context_def, computes_minimal_domain_def]
  \\ rpt(pop_assum mp_tac) \\ rw[return_def, fail_def]
  \\ rw[execution_state_component_equality] \\ gvs[]
QED

Theorem consume_gas_computes_minimal_domain[simp]:
  computes_minimal_domain (consume_gas n)
Proof
  rw[consume_gas_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem set_return_data_computes_minimal_domain[simp]:
  computes_minimal_domain (set_return_data x)
Proof
  rw[set_return_data_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem get_num_contexts_computes_minimal_domain[simp]:
  computes_minimal_domain get_num_contexts
Proof
  rw[get_num_contexts_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem get_return_data_computes_minimal_domain[simp]:
  computes_minimal_domain get_return_data
Proof
  rw[get_return_data_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem get_output_to_computes_minimal_domain[simp]:
  computes_minimal_domain get_output_to
Proof
  rw[get_output_to_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem pop_context_computes_minimal_domain[simp]:
  computes_minimal_domain pop_context
Proof
  rw[computes_minimal_domain_def, pop_context_def]
  \\ rpt(pop_assum mp_tac) \\ rw[fail_def, return_def]
  \\ rw[execution_state_component_equality]
  \\ gvs[]
QED

Theorem unuse_gas_computes_minimal_domain[simp]:
  computes_minimal_domain (unuse_gas x)
Proof
  rw[unuse_gas_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem set_rollback_computes_minimal_domain[simp]:
  computes_minimal_domain (set_rollback x)
Proof
  rw[computes_minimal_domain_def, set_rollback_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem push_logs_computes_minimal_domain[simp]:
  computes_minimal_domain (push_logs x)
Proof
  rw[push_logs_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem update_gas_refund_computes_minimal_domain[simp]:
  computes_minimal_domain (update_gas_refund x)
Proof
  Cases_on`x`
  \\ rw[update_gas_refund_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem pop_and_incorporate_context_computes_minimal_domain[simp]:
  computes_minimal_domain (pop_and_incorporate_context x)
Proof
  rw[pop_and_incorporate_context_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem inc_pc_computes_minimal_domain[simp]:
  computes_minimal_domain inc_pc
Proof
  rw[inc_pc_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem push_stack_computes_minimal_domain[simp]:
  computes_minimal_domain (push_stack x)
Proof
  rw[push_stack_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem write_memory_computes_minimal_domain[simp]:
  computes_minimal_domain (write_memory x y)
Proof
  rw[write_memory_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem handle_exception_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_exception e)
Proof
  simp[handle_exception_def]
  \\ strip_tac
  \\ irule ignore_bind_computes_minimal_domain
  \\ conj_tac
  >- (
    rw[]
    \\ irule bind_computes_minimal_domain \\ rw[]
    \\ irule ignore_bind_computes_minimal_domain \\ rw[] )
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem update_accounts_computes_minimal_domain[simp]:
  computes_minimal_domain (update_accounts x)
Proof
  rw[update_accounts_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem handle_create_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_create e)
Proof
  rw[handle_create_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem handle_step_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_step e)
Proof
  rw[handle_step_def]
  \\ irule handle_computes_minimal_domain
  \\ rw[]
  \\ gvs[handle_create_def, bind_def, get_return_data_def,
         get_current_context_def, CaseEq"prod", CaseEq"sum",
         CaseEq"bool", fail_def, return_def, get_output_to_def,
         CaseEq"return_destination", CaseEq"option",
         return_destination_CASE_rator, reraise_def,
         option_CASE_rator, assert_def, ignore_bind_def,
         consume_gas_def, set_current_context_def,
         update_accounts_def]
QED

Theorem inc_pc_or_jump_computes_minimal_domain[simp]:
  computes_minimal_domain (inc_pc_or_jump x)
Proof
  rw[inc_pc_or_jump_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem finish_computes_minimal_domain[simp]:
  computes_minimal_domain finish
Proof
  rw[finish_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem pop_stack_computes_minimal_domain[simp]:
  computes_minimal_domain (pop_stack x)
Proof
  rw[pop_stack_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_binop_computes_minimal_domain[simp]:
  computes_minimal_domain (step_binop x y)
Proof
  rw[step_binop_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_modop_computes_minimal_domain[simp]:
  computes_minimal_domain (step_modop x y)
Proof
  rw[step_modop_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_exp_computes_minimal_domain[simp]:
  computes_minimal_domain step_exp
Proof
  rw[step_exp_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_monop_computes_minimal_domain[simp]:
  computes_minimal_domain (step_monop x y)
Proof
  rw[step_monop_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem memory_expansion_info_computes_minimal_domain[simp]:
  computes_minimal_domain (memory_expansion_info x y)
Proof
  rw[memory_expansion_info_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem expand_memory_computes_minimal_domain[simp]:
  computes_minimal_domain (expand_memory x)
Proof
  rw[expand_memory_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem read_memory_computes_minimal_domain[simp]:
  computes_minimal_domain (read_memory x y)
Proof
  rw[read_memory_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_keccak256_computes_minimal_domain[simp]:
  computes_minimal_domain step_keccak256
Proof
  rw[step_keccak256_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_context_computes_minimal_domain[simp]:
  computes_minimal_domain (step_context x y)
Proof
  rw[step_context_def]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_msgParams_computes_minimal_domain[simp]:
  computes_minimal_domain (step_msgParams x y)
Proof
  rw[step_msgParams_def]
QED

Theorem domain_check_computes_minimal_domain:
  computes_minimal_domain f ∧
  (∀d. subdomain d (up d)) ∧
  (∀d. ch (up d)) ∧
  (∀d d'. ¬ch d ∧ subdomain d d' ∧ ¬subdomain (up d) d' ⇒ ¬ch d') ∧
  (∀d. ch d ⇒ up d = d) ∧
  (∀d d'. ch d ∧ subdomain d d' ⇒ ch d') ∧
  (∀s x. FST (f s) ≠ INR (SOME (OutsideDomain x)))
  ⇒
  computes_minimal_domain (domain_check err ch up f)
Proof
  rw[]
  \\ gs[computes_minimal_domain_def, domain_check_def,
        set_domain_def, ignore_bind_def, bind_def, return_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ conj_tac
  >- (
    gvs[CaseEq"domain_mode", CaseEq"bool", fail_def]
    \\ first_x_assum drule \\ rw[] )
  \\ conj_tac
  >- (
    rw[]
    \\ gvs[CaseEq"domain_mode", CaseEq"bool", fail_def]
    \\ first_x_assum drule \\ rw[]
    \\ first_x_assum(qspec_then`up d'`(CHOOSE_THEN strip_assume_tac))
    \\ rw[execution_state_component_equality]
    \\ metis_tac[subdomain_trans] )
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ gvs[CaseEq"domain_mode", CaseEq"bool", fail_def]
    \\ first_x_assum drule \\ rw[]
    \\ first_x_assum(qspec_then`up d`(CHOOSE_THEN strip_assume_tac))
    \\ gvs[]
    \\ qpat_x_assum`_ = t`(assume_tac o SYM)
    \\ gvs[]
    \\ metis_tac[subdomain_trans] )
  \\ rpt gen_tac
  \\ strip_tac
  \\ gvs[CaseEq"domain_mode", CaseEq"bool", fail_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then`up d`(CHOOSE_THEN strip_assume_tac))
  \\ gvs[]
  \\ qpat_x_assum`_ = t`(assume_tac o SYM)
  \\ gvs[]
  \\ `subdomain d d'` by metis_tac[subdomain_trans]
  \\ `ch d'` by metis_tac[]
  \\ Cases_on`ch d''` \\ gvs[]
  \\ Cases_on`ch d` \\ gvs[]
  \\ `subdomain (up d) d''` by metis_tac[]
  \\ metis_tac[]
QED

Theorem access_address_computes_minimal_domain[simp]:
  computes_minimal_domain (access_address x)
Proof
  rw[access_address_def]
  \\ irule domain_check_computes_minimal_domain
  \\ rw[]
  \\ TRY (
    gvs[subdomain_def, fIN_IN, IN_toSet_fINSERT, SUBSET_DEF]
    \\ gvs[return_def]
    \\ rw[domain_component_equality]
    \\ rw[finite_setTheory.EXTENSION, fIN_IN]
    \\ metis_tac[])
  \\ rw[computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem get_accounts_computes_minimal_domain[simp]:
  computes_minimal_domain get_accounts
Proof
  rw[get_accounts_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem step_balance_computes_minimal_domain[simp]:
  computes_minimal_domain step_balance
Proof
  rw[step_balance_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_inst_computes_minimal_domain[simp]:
  computes_minimal_domain (step_inst x)
Proof
  Cases_on`x` \\ rw[step_inst_def]
  \\ TRY (irule ignore_bind_computes_minimal_domain \\ rw[])

  \\ cheat
QED

Theorem step_computes_minimal_domain:
  computes_minimal_domain step
Proof
  rw[step_def]
  \\ irule handle_computes_minimal_domain
  \\ rw[]
  >- rw[handle_step_def, reraise_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

val () = export_theory();
