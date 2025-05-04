open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs200Theory;
val () = new_theory "vfmStateTest200";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs200";
val () = export_theory_no_docs ();
