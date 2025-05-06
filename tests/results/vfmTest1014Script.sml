open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1014Theory;
val () = new_theory "vfmTest1014";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1014") $ get_result_defs "vfmTestDefs1014";
val () = export_theory_no_docs ();
