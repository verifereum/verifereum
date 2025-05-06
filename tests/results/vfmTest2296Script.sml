open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2296Theory;
val () = new_theory "vfmTest2296";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2296") $ get_result_defs "vfmTestDefs2296";
val () = export_theory_no_docs ();
