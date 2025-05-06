open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2154Theory;
val () = new_theory "vfmTest2154";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2154") $ get_result_defs "vfmTestDefs2154";
val () = export_theory_no_docs ();
