open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2339Theory;
val () = new_theory "vfmTest2339";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2339") $ get_result_defs "vfmTestDefs2339";
val () = export_theory_no_docs ();
