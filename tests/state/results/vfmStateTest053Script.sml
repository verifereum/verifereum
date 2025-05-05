open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs053Theory;
val () = new_theory "vfmStateTest053";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs053") $ get_result_defs "vfmStateTestDefs053";
val () = export_theory_no_docs ();
