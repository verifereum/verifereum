open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0232Theory;
val () = new_theory "vfmTest0232";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0232") $ get_result_defs "vfmTestDefs0232";
val () = export_theory_no_docs ();
