open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2237Theory;
val () = new_theory "vfmTest2237";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2237") $ get_result_defs "vfmTestDefs2237";
val () = export_theory_no_docs ();
