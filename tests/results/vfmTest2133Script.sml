open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2133Theory;
val () = new_theory "vfmTest2133";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2133") $ get_result_defs "vfmTestDefs2133";
val () = export_theory_no_docs ();
