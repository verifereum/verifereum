open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs118Theory;
val () = new_theory "vfmStateTest118";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs118";
val () = export_theory_no_docs ();
