open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1514Theory;
val () = new_theory "vfmTest1514";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1514") $ get_result_defs "vfmTestDefs1514";
val () = export_theory_no_docs ();
