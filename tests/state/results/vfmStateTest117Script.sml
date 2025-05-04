open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs117Theory;
val () = new_theory "vfmStateTest117";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs117";
val () = export_theory_no_docs ();
