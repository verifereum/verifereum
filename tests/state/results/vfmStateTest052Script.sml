open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs052Theory;
val () = new_theory "vfmStateTest052";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs052") $ get_result_defs "vfmStateTestDefs052";
val () = export_theory_no_docs ();
