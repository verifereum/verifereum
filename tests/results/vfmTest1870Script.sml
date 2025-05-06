open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1870Theory;
val () = new_theory "vfmTest1870";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1870") $ get_result_defs "vfmTestDefs1870";
val () = export_theory_no_docs ();
