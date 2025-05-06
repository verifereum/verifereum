open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1141Theory;
val () = new_theory "vfmTest1141";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1141") $ get_result_defs "vfmTestDefs1141";
val () = export_theory_no_docs ();
