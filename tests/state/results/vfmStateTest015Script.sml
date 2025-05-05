open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs015Theory;
val () = new_theory "vfmStateTest015";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs015") $ get_result_defs "vfmStateTestDefs015";
val () = export_theory_no_docs ();
