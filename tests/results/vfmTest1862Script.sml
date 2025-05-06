open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1862Theory;
val () = new_theory "vfmTest1862";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1862") $ get_result_defs "vfmTestDefs1862";
val () = export_theory_no_docs ();
