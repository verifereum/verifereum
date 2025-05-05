open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs029Theory;
val () = new_theory "vfmStateTest029";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs029") $ get_result_defs "vfmStateTestDefs029";
val () = export_theory_no_docs ();
