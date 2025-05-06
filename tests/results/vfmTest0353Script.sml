open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0353Theory;
val () = new_theory "vfmTest0353";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0353") $ get_result_defs "vfmTestDefs0353";
val () = export_theory_no_docs ();
