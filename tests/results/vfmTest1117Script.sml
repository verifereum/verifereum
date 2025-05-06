open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1117Theory;
val () = new_theory "vfmTest1117";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1117") $ get_result_defs "vfmTestDefs1117";
val () = export_theory_no_docs ();
