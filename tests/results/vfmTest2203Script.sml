open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2203Theory;
val () = new_theory "vfmTest2203";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2203") $ get_result_defs "vfmTestDefs2203";
val () = export_theory_no_docs ();
