open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs161Theory;
val () = new_theory "vfmStateTest161";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs161") $ get_result_defs "vfmStateTestDefs161";
val () = export_theory_no_docs ();
