open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs111Theory;
val () = new_theory "vfmStateTest111";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs111") $ get_result_defs "vfmStateTestDefs111";
val () = export_theory_no_docs ();
