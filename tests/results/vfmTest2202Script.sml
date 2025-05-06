open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2202Theory;
val () = new_theory "vfmTest2202";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2202") $ get_result_defs "vfmTestDefs2202";
val () = export_theory_no_docs ();
