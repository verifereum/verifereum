open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1435Theory;
val () = new_theory "vfmTest1435";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1435") $ get_result_defs "vfmTestDefs1435";
val () = export_theory_no_docs ();
