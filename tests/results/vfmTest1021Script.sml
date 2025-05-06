open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1021Theory;
val () = new_theory "vfmTest1021";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1021") $ get_result_defs "vfmTestDefs1021";
val () = export_theory_no_docs ();
