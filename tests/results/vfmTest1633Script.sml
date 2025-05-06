open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1633Theory;
val () = new_theory "vfmTest1633";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1633") $ get_result_defs "vfmTestDefs1633";
val () = export_theory_no_docs ();
