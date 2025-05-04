open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs014Theory;
val () = new_theory "vfmStateTest014";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs014";
val () = export_theory_no_docs ();
