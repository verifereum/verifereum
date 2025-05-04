open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs167Theory;
val () = new_theory "vfmStateTest167";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs167";
val () = export_theory_no_docs ();
