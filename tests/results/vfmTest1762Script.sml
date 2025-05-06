open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1762Theory;
val () = new_theory "vfmTest1762";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1762") $ get_result_defs "vfmTestDefs1762";
val () = export_theory_no_docs ();
