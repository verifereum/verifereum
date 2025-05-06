open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1248Theory;
val () = new_theory "vfmTest1248";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1248") $ get_result_defs "vfmTestDefs1248";
val () = export_theory_no_docs ();
