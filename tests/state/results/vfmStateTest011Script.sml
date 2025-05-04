open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs011Theory;
val () = new_theory "vfmStateTest011";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs011";
val () = export_theory_no_docs ();
