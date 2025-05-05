open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs089Theory;
val () = new_theory "vfmStateTest089";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs089") $ get_result_defs "vfmStateTestDefs089";
val () = export_theory_no_docs ();
