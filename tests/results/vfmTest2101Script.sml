open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2101Theory;
val () = new_theory "vfmTest2101";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2101") $ get_result_defs "vfmTestDefs2101";
val () = export_theory_no_docs ();
