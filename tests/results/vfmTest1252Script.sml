open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1252Theory;
val () = new_theory "vfmTest1252";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1252") $ get_result_defs "vfmTestDefs1252";
val () = export_theory_no_docs ();
