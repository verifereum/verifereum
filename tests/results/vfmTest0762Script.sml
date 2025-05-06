open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0762Theory;
val () = new_theory "vfmTest0762";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0762") $ get_result_defs "vfmTestDefs0762";
val () = export_theory_no_docs ();
