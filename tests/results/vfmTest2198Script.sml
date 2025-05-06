open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2198Theory;
val () = new_theory "vfmTest2198";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2198") $ get_result_defs "vfmTestDefs2198";
val () = export_theory_no_docs ();
