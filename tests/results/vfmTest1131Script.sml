open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1131Theory;
val () = new_theory "vfmTest1131";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1131") $ get_result_defs "vfmTestDefs1131";
val () = export_theory_no_docs ();
