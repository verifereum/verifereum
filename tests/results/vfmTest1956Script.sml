open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1956Theory;
val () = new_theory "vfmTest1956";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1956") $ get_result_defs "vfmTestDefs1956";
val () = export_theory_no_docs ();
