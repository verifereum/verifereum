open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs055Theory;
val () = new_theory "vfmStateTest055";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs055") $ get_result_defs "vfmStateTestDefs055";
val () = export_theory_no_docs ();
