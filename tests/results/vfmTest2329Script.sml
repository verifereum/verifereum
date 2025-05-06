open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2329Theory;
val () = new_theory "vfmTest2329";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2329") $ get_result_defs "vfmTestDefs2329";
val () = export_theory_no_docs ();
