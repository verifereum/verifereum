open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1480Theory;
val () = new_theory "vfmTest1480";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1480") $ get_result_defs "vfmTestDefs1480";
val () = export_theory_no_docs ();
