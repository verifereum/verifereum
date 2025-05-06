open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0329Theory;
val () = new_theory "vfmTest0329";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0329") $ get_result_defs "vfmTestDefs0329";
val () = export_theory_no_docs ();
