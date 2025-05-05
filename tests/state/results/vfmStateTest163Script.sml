open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs163Theory;
val () = new_theory "vfmStateTest163";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs163") $ get_result_defs "vfmStateTestDefs163";
val () = export_theory_no_docs ();
