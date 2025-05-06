open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0833Theory;
val () = new_theory "vfmTest0833";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0833") $ get_result_defs "vfmTestDefs0833";
val () = export_theory_no_docs ();
