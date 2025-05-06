open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2299Theory;
val () = new_theory "vfmTest2299";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2299") $ get_result_defs "vfmTestDefs2299";
val () = export_theory_no_docs ();
