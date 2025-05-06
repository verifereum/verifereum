open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2609Theory;
val () = new_theory "vfmTest2609";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2609") $ get_result_defs "vfmTestDefs2609";
val () = export_theory_no_docs ();
