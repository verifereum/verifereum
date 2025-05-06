open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1903Theory;
val () = new_theory "vfmTest1903";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1903") $ get_result_defs "vfmTestDefs1903";
val () = export_theory_no_docs ();
