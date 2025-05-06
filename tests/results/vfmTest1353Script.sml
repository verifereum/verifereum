open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1353Theory;
val () = new_theory "vfmTest1353";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1353") $ get_result_defs "vfmTestDefs1353";
val () = export_theory_no_docs ();
