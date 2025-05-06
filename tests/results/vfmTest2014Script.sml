open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2014Theory;
val () = new_theory "vfmTest2014";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2014") $ get_result_defs "vfmTestDefs2014";
val () = export_theory_no_docs ();
