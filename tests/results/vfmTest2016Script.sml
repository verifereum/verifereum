open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2016Theory;
val () = new_theory "vfmTest2016";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2016") $ get_result_defs "vfmTestDefs2016";
val () = export_theory_no_docs ();
