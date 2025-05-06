open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1164Theory;
val () = new_theory "vfmTest1164";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1164") $ get_result_defs "vfmTestDefs1164";
val () = export_theory_no_docs ();
