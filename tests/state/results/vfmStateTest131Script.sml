open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs131Theory;
val () = new_theory "vfmStateTest131";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs131") $ get_result_defs "vfmStateTestDefs131";
val () = export_theory_no_docs ();
