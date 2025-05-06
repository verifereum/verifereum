open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0754Theory;
val () = new_theory "vfmTest0754";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0754") $ get_result_defs "vfmTestDefs0754";
val () = export_theory_no_docs ();
