open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1177Theory;
val () = new_theory "vfmTest1177";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1177") $ get_result_defs "vfmTestDefs1177";
val () = export_theory_no_docs ();
