open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2633Theory;
val () = new_theory "vfmTest2633";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2633") $ get_result_defs "vfmTestDefs2633";
val () = export_theory_no_docs ();
