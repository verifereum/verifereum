open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2563Theory;
val () = new_theory "vfmTest2563";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2563") $ get_result_defs "vfmTestDefs2563";
val () = export_theory_no_docs ();
