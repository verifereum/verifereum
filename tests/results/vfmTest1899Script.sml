open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1899Theory;
val () = new_theory "vfmTest1899";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1899") $ get_result_defs "vfmTestDefs1899";
val () = export_theory_no_docs ();
