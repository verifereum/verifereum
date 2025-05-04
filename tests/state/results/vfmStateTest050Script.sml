open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs050Theory;
val () = new_theory "vfmStateTest050";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs050";
val () = export_theory_no_docs ();
