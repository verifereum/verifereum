open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2166Theory;
val () = new_theory "vfmTest2166";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2166") $ get_result_defs "vfmTestDefs2166";
val () = export_theory_no_docs ();
