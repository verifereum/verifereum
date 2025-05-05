open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs100Theory;
val () = new_theory "vfmStateTest100";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs100") $ get_result_defs "vfmStateTestDefs100";
val () = export_theory_no_docs ();
