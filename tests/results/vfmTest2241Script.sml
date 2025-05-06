open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2241Theory;
val () = new_theory "vfmTest2241";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2241") $ get_result_defs "vfmTestDefs2241";
val () = export_theory_no_docs ();
