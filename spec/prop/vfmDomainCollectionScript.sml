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

Theorem get_tx_params_computes_minimal_domain[simp]:
  computes_minimal_domain get_tx_params
Proof
  rw[get_tx_params_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem step_txParams_computes_minimal_domain[simp]:
  computes_minimal_domain (step_txParams x y)
Proof
  rw[step_txParams_def]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem get_call_data_computes_minimal_domain[simp]:
  computes_minimal_domain get_call_data
Proof
  rw[get_call_data_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_call_data_load_computes_minimal_domain[simp]:
  computes_minimal_domain step_call_data_load
Proof
  rw[step_call_data_load_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_ext_code_size_computes_minimal_domain[simp]:
  computes_minimal_domain step_ext_code_size
Proof
  rw[step_ext_code_size_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem copy_to_memory_computes_minimal_domain[simp]:
  (∀f. b = SOME f ⇒ computes_minimal_domain f) ⇒
  computes_minimal_domain (copy_to_memory x y z a b)
Proof
  rw[copy_to_memory_def, UNCURRY]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ TRY TOP_CASE_TAC \\ gvs[]
  \\ TRY (irule ignore_bind_computes_minimal_domain \\ rw[])
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem get_code_computes_minimal_domain[simp]:
  computes_minimal_domain (get_code x)
Proof
  rw[get_code_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_ext_code_copy_computes_minimal_domain[simp]:
  computes_minimal_domain step_ext_code_copy
Proof
  rw[step_ext_code_copy_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule copy_to_memory_computes_minimal_domain \\ rw[]
QED

Theorem get_current_code_computes_minimal_domain[simp]:
  computes_minimal_domain get_current_code
Proof
  rw[get_current_code_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_copy_to_memory_computes_minimal_domain[simp]:
  (∀f. b = SOME f ⇒ computes_minimal_domain f) ⇒
  computes_minimal_domain (step_copy_to_memory x b)
Proof
  rw[step_copy_to_memory_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem get_return_data_check_computes_minimal_domain[simp]:
  computes_minimal_domain (get_return_data_check x y)
Proof
  rw[get_return_data_check_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_return_data_copy_computes_minimal_domain[simp]:
  computes_minimal_domain step_return_data_copy
Proof
  rw[step_return_data_copy_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_ext_code_hash_computes_minimal_domain[simp]:
  computes_minimal_domain step_ext_code_hash
Proof
  rw[step_ext_code_hash_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_block_hash_computes_minimal_domain[simp]:
  computes_minimal_domain step_block_hash
Proof
  rw[step_block_hash_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_blob_hash_computes_minimal_domain[simp]:
  computes_minimal_domain step_blob_hash
Proof
  rw[step_blob_hash_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem get_callee_computes_minimal_domain[simp]:
  computes_minimal_domain get_callee
Proof
  rw[get_callee_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_self_balance_computes_minimal_domain[simp]:
  computes_minimal_domain step_self_balance
Proof
  rw[step_self_balance_def]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_pop_computes_minimal_domain[simp]:
  computes_minimal_domain step_pop
Proof
  rw[step_pop_def]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_mload_computes_minimal_domain[simp]:
  computes_minimal_domain step_mload
Proof
  rw[step_mload_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

Theorem step_mstore_computes_minimal_domain[simp]:
  computes_minimal_domain (step_mstore x)
Proof
  rw[step_mstore_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem get_tStorage_computes_minimal_domain[simp]:
  computes_minimal_domain get_tStorage
Proof
  rw[get_tStorage_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem access_slot_computes_minimal_domain[simp]:
  computes_minimal_domain (access_slot x)
Proof
  rw[access_slot_def]
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

Theorem step_sload_computes_minimal_domain[simp]:
  computes_minimal_domain (step_sload x)
Proof
  rw[step_sload_def]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ TRY $ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
  \\ irule bind_computes_minimal_domain \\ rw[]
QED

val tac = rpt (
  (irule ignore_bind_computes_minimal_domain \\ rw[])
  ORELSE
  (irule bind_computes_minimal_domain \\ rw[]));

Theorem get_original_computes_minimal_domain[simp]:
  computes_minimal_domain get_original
Proof
  rw[get_original_def, computes_minimal_domain_def, return_def]
  \\ rpt(pop_assum mp_tac) \\ rw[fail_def]
  \\ rw[execution_state_component_equality]
QED

Theorem step_sstore_gas_consumption_computes_minimal_domain[simp]:
  computes_minimal_domain (step_sstore_gas_consumption x y z)
Proof
  rw[step_sstore_gas_consumption_def]
  \\ tac
QED

Theorem get_static_computes_minimal_domain[simp]:
  computes_minimal_domain get_static
Proof
  rw[get_static_def] \\ tac
QED

Theorem assert_not_static_computes_minimal_domain[simp]:
  computes_minimal_domain assert_not_static
Proof
  rw[assert_not_static_def] \\ tac
QED

Theorem write_storage_computes_minimal_domain[simp]:
  computes_minimal_domain (write_storage x y z)
Proof
  rw[write_storage_def] \\ tac
QED

Theorem set_tStorage_computes_minimal_domain[simp]:
  computes_minimal_domain (set_tStorage x)
Proof
  rw[set_tStorage_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem write_transient_storage_computes_minimal_domain[simp]:
  computes_minimal_domain (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def] \\ tac
QED

Theorem step_sstore_computes_minimal_domain[simp]:
  computes_minimal_domain (step_sstore x)
Proof
  rw[step_sstore_def] \\ tac
QED

Theorem set_jump_dest_computes_minimal_domain[simp]:
  computes_minimal_domain (set_jump_dest x)
Proof
  rw[set_jump_dest_def] \\ tac
QED

Theorem step_jump_computes_minimal_domain[simp]:
  computes_minimal_domain step_jump
Proof
  rw[step_jump_def] \\ tac
QED

Theorem step_jumpi_computes_minimal_domain[simp]:
  computes_minimal_domain step_jumpi
Proof
  rw[step_jumpi_def] \\ tac
QED

Theorem step_push_computes_minimal_domain[simp]:
  computes_minimal_domain (step_push x y)
Proof
  rw[step_push_def] \\ tac
QED

Theorem step_swap_computes_minimal_domain[simp]:
  computes_minimal_domain (step_swap n)
Proof
  rw[step_swap_def] \\ tac
QED

Theorem step_dup_computes_minimal_domain[simp]:
  computes_minimal_domain (step_dup n)
Proof
  rw[step_dup_def] \\ tac
QED

Theorem step_log_computes_minimal_domain[simp]:
  computes_minimal_domain (step_log x)
Proof
  rw[step_log_def] \\ tac
QED

Theorem abort_unuse_computes_minimal_domain[simp]:
  computes_minimal_domain (abort_unuse x)
Proof
  rw[abort_unuse_def] \\ tac
QED

Theorem ensure_storage_in_domain_computes_minimal_domain[simp]:
  computes_minimal_domain (ensure_storage_in_domain x)
Proof
  rw[ensure_storage_in_domain_def]
  \\ irule domain_check_computes_minimal_domain
  \\ rw[]
  \\ gvs[subdomain_def, fIN_IN, IN_toSet_fINSERT, SUBSET_DEF]
  \\ rw[domain_component_equality, return_def]
  \\ rw[finite_setTheory.EXTENSION, fIN_IN]
  \\ metis_tac[]
QED

Theorem abort_create_exists_computes_minimal_domain[simp]:
  computes_minimal_domain (abort_create_exists x)
Proof
  rw[abort_create_exists_def] \\ tac
QED

Theorem get_rollback_computes_minimal_domain[simp]:
  computes_minimal_domain get_rollback
Proof
  rw[get_rollback_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem push_context_computes_minimal_domain[simp]:
  computes_minimal_domain (push_context x)
Proof
  rw[push_context_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem set_original_computes_minimal_domain[simp]:
  computes_minimal_domain (set_original a)
Proof
  rw[computes_minimal_domain_def, set_original_def]
  \\ gvs[CaseEq"bool", CaseEq"prod", fail_def, return_def]
  \\ gvs[execution_state_component_equality]
QED

Theorem proceed_create_computes_minimal_domain[simp]:
  computes_minimal_domain (proceed_create a b c d e)
Proof
  rw[proceed_create_def] \\ tac
QED

Theorem step_create_computes_minimal_domain[simp]:
  computes_minimal_domain (step_create x)
Proof
  rw[step_create_def] \\ tac
QED

Theorem abort_call_value_computes_minimal_domain[simp]:
  computes_minimal_domain (abort_call_value x)
Proof
  rw[abort_call_value_def] \\ tac
QED

Theorem get_caller_computes_minimal_domain[simp]:
  computes_minimal_domain get_caller
Proof
  rw[get_caller_def] \\ tac
QED

Theorem get_value_computes_minimal_domain[simp]:
  computes_minimal_domain get_value
Proof
  rw[get_value_def] \\ tac
QED

Theorem revert_computes_minimal_domain[simp]:
  computes_minimal_domain revert
Proof
  rw[revert_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem precompiles_compute_minimal_domain[simp]:
  computes_minimal_domain precompile_sha2_256 ∧
  computes_minimal_domain precompile_ripemd_160 ∧
  computes_minimal_domain precompile_identity ∧
  computes_minimal_domain precompile_modexp ∧
  computes_minimal_domain precompile_ecadd ∧
  computes_minimal_domain precompile_ecmul ∧
  computes_minimal_domain precompile_ecpairing ∧
  computes_minimal_domain precompile_blake2f ∧
  computes_minimal_domain precompile_ecrecover ∧
  computes_minimal_domain precompile_point_eval
Proof
  rw[precompile_sha2_256_def, precompile_ripemd_160_def,
     precompile_identity_def, precompile_modexp_def,
     precompile_ecadd_def, precompile_ecmul_def,
     precompile_ecpairing_def, precompile_blake2f_def,
     precompile_ecrecover_def, precompile_point_eval_def]
  \\ tac
  \\ CASE_TAC \\ rw[]
  \\ TRY CASE_TAC
  \\ tac
QED


Theorem dispatch_precompiles_computes_minimal_domain[simp]:
  computes_minimal_domain (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem proceed_call_computes_minimal_domain[simp]:
  computes_minimal_domain (proceed_call a b c d e f g h i)
Proof
  rw[proceed_call_def] \\ tac
QED

Theorem step_call_computes_minimal_domain[simp]:
  computes_minimal_domain (step_call x)
Proof
  rw[step_call_def, UNCURRY] \\ tac
QED

Theorem step_return_computes_minimal_domain[simp]:
  computes_minimal_domain (step_return x)
Proof
  rw[step_return_def] \\ tac
QED

Theorem step_invalid_computes_minimal_domain[simp]:
  computes_minimal_domain step_invalid
Proof
  rw[step_invalid_def] \\ tac
QED

Theorem add_to_delete_computes_minimal_domain[simp]:
  computes_minimal_domain (add_to_delete x)
Proof
  rw[add_to_delete_def, computes_minimal_domain_def, return_def]
  \\ rw[execution_state_component_equality]
QED

Theorem step_self_destruct_computes_minimal_domain[simp]:
  computes_minimal_domain step_self_destruct
Proof
  rw[step_self_destruct_def] \\ tac
QED

Theorem step_inst_computes_minimal_domain[simp]:
  computes_minimal_domain (step_inst x)
Proof
  Cases_on`x` \\ rw[step_inst_def]
  \\ irule ignore_bind_computes_minimal_domain \\ rw[]
QED

Theorem step_computes_minimal_domain[simp]:
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
