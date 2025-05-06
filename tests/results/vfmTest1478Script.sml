open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1478Theory;
val () = new_theory "vfmTest1478";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1478") $ get_result_defs "vfmTestDefs1478";
val () = export_theory_no_docs ();
