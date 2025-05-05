open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs140Theory;
val () = new_theory "vfmStateTest140";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs140") $ get_result_defs "vfmStateTestDefs140";
val () = export_theory_no_docs ();
