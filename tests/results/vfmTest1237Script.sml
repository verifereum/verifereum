open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1237Theory;
val () = new_theory "vfmTest1237";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1237") $ get_result_defs "vfmTestDefs1237";
val () = export_theory_no_docs ();
