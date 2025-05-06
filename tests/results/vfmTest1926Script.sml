open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1926Theory;
val () = new_theory "vfmTest1926";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1926") $ get_result_defs "vfmTestDefs1926";
val () = export_theory_no_docs ();
