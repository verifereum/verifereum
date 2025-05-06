open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1142Theory;
val () = new_theory "vfmTest1142";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1142") $ get_result_defs "vfmTestDefs1142";
val () = export_theory_no_docs ();
