open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0083Theory;
val () = new_theory "vfmTest0083";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0083") $ get_result_defs "vfmTestDefs0083";
val () = export_theory_no_docs ();
