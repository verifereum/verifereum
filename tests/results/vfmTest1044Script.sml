open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1044Theory;
val () = new_theory "vfmTest1044";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1044") $ get_result_defs "vfmTestDefs1044";
val () = export_theory_no_docs ();
