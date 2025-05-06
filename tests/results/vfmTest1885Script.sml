open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1885Theory;
val () = new_theory "vfmTest1885";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1885") $ get_result_defs "vfmTestDefs1885";
val () = export_theory_no_docs ();
