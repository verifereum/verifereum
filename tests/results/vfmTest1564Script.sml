open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1564Theory;
val () = new_theory "vfmTest1564";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1564") $ get_result_defs "vfmTestDefs1564";
val () = export_theory_no_docs ();
