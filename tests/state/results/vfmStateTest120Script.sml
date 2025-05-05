open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs120Theory;
val () = new_theory "vfmStateTest120";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs120") $ get_result_defs "vfmStateTestDefs120";
val () = export_theory_no_docs ();
