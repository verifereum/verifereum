open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2177Theory;
val () = new_theory "vfmTest2177";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2177") $ get_result_defs "vfmTestDefs2177";
val () = export_theory_no_docs ();
