open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2164Theory;
val () = new_theory "vfmTest2164";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2164") $ get_result_defs "vfmTestDefs2164";
val () = export_theory_no_docs ();
