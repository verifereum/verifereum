open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1652Theory;
val () = new_theory "vfmTest1652";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1652") $ get_result_defs "vfmTestDefs1652";
val () = export_theory_no_docs ();
