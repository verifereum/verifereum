open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs039Theory;
val () = new_theory "vfmStateTest039";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs039") $ get_result_defs "vfmStateTestDefs039";
val () = export_theory_no_docs ();
