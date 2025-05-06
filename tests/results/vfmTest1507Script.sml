open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1507Theory;
val () = new_theory "vfmTest1507";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1507") $ get_result_defs "vfmTestDefs1507";
val () = export_theory_no_docs ();
