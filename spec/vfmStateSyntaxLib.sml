structure vfmStateSyntaxLib :> vfmStateSyntaxLib = struct

  open vfmStateTheory vfmTypesSyntaxLib

  val account_ty = mk_thy_type{Thy="vfmState",Tyop="account_state", Args=[]}
  val accounts_ty = address_ty --> account_ty

end
