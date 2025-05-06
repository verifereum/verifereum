open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1118Theory;
val () = new_theory "vfmTest1118";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1118") $ get_result_defs "vfmTestDefs1118";
val () = export_theory_no_docs ();
