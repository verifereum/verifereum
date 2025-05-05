open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs153Theory;
val () = new_theory "vfmStateTest153";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs153") $ get_result_defs "vfmStateTestDefs153";
val () = export_theory_no_docs ();
