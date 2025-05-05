open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs192Theory;
val () = new_theory "vfmStateTest192";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs192") $ get_result_defs "vfmStateTestDefs192";
val () = export_theory_no_docs ();
