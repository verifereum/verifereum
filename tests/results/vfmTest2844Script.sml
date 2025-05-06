open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2844Theory;
val () = new_theory "vfmTest2844";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2844") $ get_result_defs "vfmTestDefs2844";
val () = export_theory_no_docs ();
