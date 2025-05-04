open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs112Theory;
val () = new_theory "vfmStateTest112";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs112";
val () = export_theory_no_docs ();
