open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs079Theory;
val () = new_theory "vfmStateTest079";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs079";
val () = export_theory_no_docs ();
