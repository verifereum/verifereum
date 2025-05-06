open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0154Theory;
val () = new_theory "vfmTest0154";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0154") $ get_result_defs "vfmTestDefs0154";
val () = export_theory_no_docs ();
