open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2888Theory;
val () = new_theory "vfmTest2888";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2888") $ get_result_defs "vfmTestDefs2888";
val () = export_theory_no_docs ();
