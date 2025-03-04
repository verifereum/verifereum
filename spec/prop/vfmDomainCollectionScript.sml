open HolKernel boolLib bossLib Parse BasicProvers
     vfmExecutionTheory
     vfmContextTheory vfmDomainSeparationTheory;

val () = new_theory "vfmDomainCollection";

(*

not sure if worth splitting these

Definition extends_domain_def:
  extends_domain m =
  ∀s r t d. m s = (r, t) ∧ s.msdomain = Collect d ⇒
    (∀x. r ≠ INR (SOME (OutsideDomain x))) ∧
    (∀d'. ∃d''.
       m (s with msdomain := Collect d') =
       (r, t with msdomain := Collect d'') ∧
       subdomain d' d'')
End

Definition computes_enforceable_def:
  computes_enforceable m =
  ∀s r t d'.
    m s = (r, t) ∧ t.msdomain = Collect d'
    ⇒
    m (s with msdomain := Enforce d') =
    (r, t with msdomain := Enforce d')
End

Definition computes_minimal_def:
  computes_minimal m =
  ∀s r t d d'.
    m s = (r, t) ∧
    s.msdomain = Collect d ∧
    t.msdomain = Collect d'
    ⇒

    ∃d'. t.msdomain = Collect d' ∧ subdomain d d' ∧
         ∀d''. subdomain d d'' ⇒
           ∃r'. m (s with msdomain := Enforce d'') =
                  (r', t with msdomain := Enforce d'') ∧
                (∀x. r' = INR (SOME (OutsideDomain x)) ⇒
                     ¬subdomain d' d'') ∧
                ((∀x. r' ≠ INR (SOME (OutsideDomain x))) ⇒
                 (r' = r ∧ subdomain d' d''))
End

Definition ecmd_def:
  ecmd m ⇔ extends_domain m ∧ computes_minimal_domain m
End

*)

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

(*
Proof
  rw[bind_def, ecmd_def, extends_domain_def, computes_minimal_domain_def, CaseEq"prod"]
  >- (
    first_x_assum(drule_then drule)
    \\ gs[CaseEq"sum"] \\ rw[]
    \\ first_x_assum (drule_then drule)
    \\ rw[]
    \\ metis_tac[])
  >- (
    fsrw_tac[DNF_ss][PULL_EXISTS]
    \\ last_x_assum(drule_then (drule_then $ qspec_then`d'`strip_assume_tac))
    \\ rw[]
    \\ reverse CASE_TAC \\ gvs[]
    >- rw[execution_state_component_equality]
    \\ last_x_assum(drule_then drule) \\ strip_tac
    \\ last_x_assum(drule_then drule) \\ strip_tac
    \\ metis_tac[subdomain_trans] )
  \\ reverse(Cases_on`v`) \\ gvs[]
  >- (
    fsrw_tac[DNF_ss][]
    \\ first_assum(drule_then drule)
    \\ strip_tac \\ simp[]
    \\ rpt gen_tac \\ strip_tac
    \\ first_assum drule \\ strip_tac
    \\ simp[] \\ Cases_on`r'` \\ gvs[] )
  \\ first_assum (drule_then drule)
  \\ strip_tac
  \\ fsrw_tac[DNF_ss][]
  \\ first_assum (drule_then drule)
  \\ strip_tac
  \\ simp[]
  \\ conj_tac >- metis_tac[subdomain_trans]
  \\ gen_tac \\ strip_tac
  \\ first_assum (drule_then(fn th =>
       strip_assume_tac th \\ CHANGED_TAC(simp[])))
  \\ Cases_on`r'` \\ gvs[]
*)

(*
Theorem step_computes_minimal_domain:
  computes_minimal_domain step
Proof
  rw[step_def]
*)

val () = export_theory();
