open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2018Theory;
val () = new_theory "vfmTest2018";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2018") $ get_result_defs "vfmTestDefs2018";
val () = export_theory_no_docs ();
