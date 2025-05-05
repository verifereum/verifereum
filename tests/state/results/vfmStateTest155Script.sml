open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs155Theory;
val () = new_theory "vfmStateTest155";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs155") $ get_result_defs "vfmStateTestDefs155";
val () = export_theory_no_docs ();
