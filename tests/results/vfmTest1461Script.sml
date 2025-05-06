open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1461Theory;
val () = new_theory "vfmTest1461";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1461") $ get_result_defs "vfmTestDefs1461";
val () = export_theory_no_docs ();
