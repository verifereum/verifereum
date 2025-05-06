open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2086Theory;
val () = new_theory "vfmTest2086";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2086") $ get_result_defs "vfmTestDefs2086";
val () = export_theory_no_docs ();
