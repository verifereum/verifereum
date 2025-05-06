open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1557Theory;
val () = new_theory "vfmTest1557";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1557") $ get_result_defs "vfmTestDefs1557";
val () = export_theory_no_docs ();
