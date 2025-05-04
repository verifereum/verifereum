open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs071Theory;
val () = new_theory "vfmStateTest071";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs071";
val () = export_theory_no_docs ();
