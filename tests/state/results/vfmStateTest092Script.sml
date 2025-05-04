open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs092Theory;
val () = new_theory "vfmStateTest092";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs092";
val () = export_theory_no_docs ();
