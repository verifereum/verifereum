open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0614Theory;
val () = new_theory "vfmTest0614";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0614") $ get_result_defs "vfmTestDefs0614";
val () = export_theory_no_docs ();
