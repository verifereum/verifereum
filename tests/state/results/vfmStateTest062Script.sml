open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs062Theory;
val () = new_theory "vfmStateTest062";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs062";
val () = export_theory_no_docs ();
