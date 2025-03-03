open HolKernel boolLib bossLib Parse
     vfmExecutionTheory
     vfmDomainSeparationTheory;

val () = new_theory "vfmDomainCollection";

Definition computes_minimal_domain_def:
  computes_minimal_domain m =
  ∀s r t d. m s = (r, t) ∧ s.msdomain = Collect d ⇒
    ∃d'. t.msdomain = Collect d' ∧ subdomain d d' ∧
         m (s with msdomain := Enforce d') =
           (r, t with msdomain := Enforce d') ∧
         ∀d''. subdomain d d'' ∧
           m (s with msdomain := Enforce d'') =
             (r, t with msdomain := Enforce d'')
           ⇒ subdomain d' d''
End

Theorem fail_computes_minimal_domain[simp]:
  computes_minimal_domain (fail x)
Proof
  rw[computes_minimal_domain_def, fail_def]
QED

Theorem return_computes_minimal_domain[simp]:
  computes_minimal_domain (return x)
Proof
  rw[computes_minimal_domain_def, return_def]
QED

Theorem get_current_context_computes_minimal_domain[simp]:
  computes_minimal_domain get_current_context
Proof
  rw[computes_minimal_domain_def, get_current_context_def]
  \\ CASE_TAC \\ gvs[return_def, fail_def]
QED

(*
Theorem step_computes_minimal_domain:
  computes_minimal_domain step
Proof
  rw[step_def]
*)

val () = export_theory();
