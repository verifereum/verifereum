open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1494Theory;
val () = new_theory "vfmTest1494";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1494") $ get_result_defs "vfmTestDefs1494";
val () = export_theory_no_docs ();
