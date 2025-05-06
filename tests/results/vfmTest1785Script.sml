open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1785Theory;
val () = new_theory "vfmTest1785";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1785") $ get_result_defs "vfmTestDefs1785";
val () = export_theory_no_docs ();
