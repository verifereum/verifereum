open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs024Theory;
val () = new_theory "vfmStateTest024";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs024";
val () = export_theory_no_docs ();
