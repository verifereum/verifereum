open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2035Theory;
val () = new_theory "vfmTest2035";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2035") $ get_result_defs "vfmTestDefs2035";
val () = export_theory_no_docs ();
