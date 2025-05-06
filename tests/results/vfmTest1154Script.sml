open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1154Theory;
val () = new_theory "vfmTest1154";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1154") $ get_result_defs "vfmTestDefs1154";
val () = export_theory_no_docs ();
