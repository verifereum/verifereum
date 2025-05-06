open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1364Theory;
val () = new_theory "vfmTest1364";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1364") $ get_result_defs "vfmTestDefs1364";
val () = export_theory_no_docs ();
