open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs040Theory;
val () = new_theory "vfmStateTest040";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs040";
val () = export_theory_no_docs ();
