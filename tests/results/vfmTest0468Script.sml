open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0468Theory;
val () = new_theory "vfmTest0468";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0468") $ get_result_defs "vfmTestDefs0468";
val () = export_theory_no_docs ();
