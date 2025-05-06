open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1410Theory;
val () = new_theory "vfmTest1410";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1410") $ get_result_defs "vfmTestDefs1410";
val () = export_theory_no_docs ();
