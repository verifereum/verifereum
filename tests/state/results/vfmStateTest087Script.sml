open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs087Theory;
val () = new_theory "vfmStateTest087";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs087") $ get_result_defs "vfmStateTestDefs087";
val () = export_theory_no_docs ();
