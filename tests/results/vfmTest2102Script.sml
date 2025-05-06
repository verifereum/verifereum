open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2102Theory;
val () = new_theory "vfmTest2102";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2102") $ get_result_defs "vfmTestDefs2102";
val () = export_theory_no_docs ();
