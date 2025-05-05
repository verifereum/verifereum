open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs017Theory;
val () = new_theory "vfmStateTest017";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs017") $ get_result_defs "vfmStateTestDefs017";
val () = export_theory_no_docs ();
