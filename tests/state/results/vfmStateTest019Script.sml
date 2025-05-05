open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs019Theory;
val () = new_theory "vfmStateTest019";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs019") $ get_result_defs "vfmStateTestDefs019";
val () = export_theory_no_docs ();
