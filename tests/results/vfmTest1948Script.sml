open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1948Theory;
val () = new_theory "vfmTest1948";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1948") $ get_result_defs "vfmTestDefs1948";
val () = export_theory_no_docs ();
