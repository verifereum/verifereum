open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1675Theory;
val () = new_theory "vfmTest1675";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1675") $ get_result_defs "vfmTestDefs1675";
val () = export_theory_no_docs ();
