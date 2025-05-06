open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1744Theory;
val () = new_theory "vfmTest1744";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1744") $ get_result_defs "vfmTestDefs1744";
val () = export_theory_no_docs ();
