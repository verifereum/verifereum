open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs186Theory;
val () = new_theory "vfmStateTest186";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs186") $ get_result_defs "vfmStateTestDefs186";
val () = export_theory_no_docs ();
