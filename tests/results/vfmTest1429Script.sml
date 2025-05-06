open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1429Theory;
val () = new_theory "vfmTest1429";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1429") $ get_result_defs "vfmTestDefs1429";
val () = export_theory_no_docs ();
