open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs095Theory;
val () = new_theory "vfmStateTest095";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs095") $ get_result_defs "vfmStateTestDefs095";
val () = export_theory_no_docs ();
