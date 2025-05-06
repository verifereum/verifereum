open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1666Theory;
val () = new_theory "vfmTest1666";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1666") $ get_result_defs "vfmTestDefs1666";
val () = export_theory_no_docs ();
