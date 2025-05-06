open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1944Theory;
val () = new_theory "vfmTest1944";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1944") $ get_result_defs "vfmTestDefs1944";
val () = export_theory_no_docs ();
