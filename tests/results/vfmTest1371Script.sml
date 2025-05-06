open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1371Theory;
val () = new_theory "vfmTest1371";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1371") $ get_result_defs "vfmTestDefs1371";
val () = export_theory_no_docs ();
