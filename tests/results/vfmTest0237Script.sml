open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0237Theory;
val () = new_theory "vfmTest0237";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0237") $ get_result_defs "vfmTestDefs0237";
val () = export_theory_no_docs ();
