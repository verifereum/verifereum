open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0144Theory;
val () = new_theory "vfmTest0144";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0144") $ get_result_defs "vfmTestDefs0144";
val () = export_theory_no_docs ();
