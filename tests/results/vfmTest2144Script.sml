open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2144Theory;
val () = new_theory "vfmTest2144";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2144") $ get_result_defs "vfmTestDefs2144";
val () = export_theory_no_docs ();
