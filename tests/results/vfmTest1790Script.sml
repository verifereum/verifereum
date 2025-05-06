open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1790Theory;
val () = new_theory "vfmTest1790";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1790") $ get_result_defs "vfmTestDefs1790";
val () = export_theory_no_docs ();
