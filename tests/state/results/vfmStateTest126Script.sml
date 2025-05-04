open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs126Theory;
val () = new_theory "vfmStateTest126";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs126";
val () = export_theory_no_docs ();
