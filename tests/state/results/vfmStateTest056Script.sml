open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs056Theory;
val () = new_theory "vfmStateTest056";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs056") $ get_result_defs "vfmStateTestDefs056";
val () = export_theory_no_docs ();
