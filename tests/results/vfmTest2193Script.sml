open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2193Theory;
val () = new_theory "vfmTest2193";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2193") $ get_result_defs "vfmTestDefs2193";
val () = export_theory_no_docs ();
