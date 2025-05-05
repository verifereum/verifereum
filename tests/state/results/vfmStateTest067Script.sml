open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs067Theory;
val () = new_theory "vfmStateTest067";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs067") $ get_result_defs "vfmStateTestDefs067";
val () = export_theory_no_docs ();
