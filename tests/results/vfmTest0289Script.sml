open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0289Theory;
val () = new_theory "vfmTest0289";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0289") $ get_result_defs "vfmTestDefs0289";
val () = export_theory_no_docs ();
