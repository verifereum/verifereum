open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1050Theory;
val () = new_theory "vfmTest1050";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1050") $ get_result_defs "vfmTestDefs1050";
val () = export_theory_no_docs ();
