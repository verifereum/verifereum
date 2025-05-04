open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs006Theory;
val () = new_theory "vfmStateTest006";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs006";
val () = export_theory_no_docs ();
