open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs037Theory;
val () = new_theory "vfmStateTest037";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs037";
val () = export_theory_no_docs ();
