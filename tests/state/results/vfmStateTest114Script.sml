open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs114Theory;
val () = new_theory "vfmStateTest114";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs114") $ get_result_defs "vfmStateTestDefs114";
val () = export_theory_no_docs ();
