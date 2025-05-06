open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0218Theory;
val () = new_theory "vfmTest0218";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0218") $ get_result_defs "vfmTestDefs0218";
val () = export_theory_no_docs ();
