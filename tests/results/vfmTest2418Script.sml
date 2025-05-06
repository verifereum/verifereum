open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2418Theory;
val () = new_theory "vfmTest2418";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2418") $ get_result_defs "vfmTestDefs2418";
val () = export_theory_no_docs ();
