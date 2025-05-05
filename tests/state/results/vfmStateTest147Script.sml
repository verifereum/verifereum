open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs147Theory;
val () = new_theory "vfmStateTest147";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs147") $ get_result_defs "vfmStateTestDefs147";
val () = export_theory_no_docs ();
