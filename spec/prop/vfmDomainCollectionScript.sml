open HolKernel boolLib bossLib Parse BasicProvers
     pairTheory
     vfmExecutionTheory
     vfmContextTheory vfmDomainSeparationTheory;

val () = new_theory "vfmDomainCollection";

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

(*
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


Theorem handle_step_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_step e)
Proof
  rw[handle_step_def]
  \\ irule handle_computes_minimal_domain
  \\ rw[]
  >- (
    gvs[handle_create_def, bind_def, get_return_data_def,
        get_current_context_def, CaseEq"prod", CaseEq"sum",
        CaseEq"bool", fail_def, return_def, get_output_to_def,
        CaseEq"return_destination", CaseEq"option",
        return_destination_CASE_rator, reraise_def,
        option_CASE_rator, assert_def, ignore_bind_def,
        consume_gas_def, set_current_context_def,
        update_accounts_def] )
  >- (


Theorem step_computes_minimal_domain:
  computes_minimal_domain step
Proof
  rw[step_def]
  \\ irule handle_computes_minimal_domain
  \\ conj_tac
  >- rw[handle_step_def, reraise_def]
  \\ conj_tac
  >- (
  \\ cheat
QED
*)

val () = export_theory();
