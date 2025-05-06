open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2338Theory;
val () = new_theory "vfmTest2338";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2338") $ get_result_defs "vfmTestDefs2338";
val () = export_theory_no_docs ();
