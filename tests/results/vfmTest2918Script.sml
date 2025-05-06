open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2918Theory;
val () = new_theory "vfmTest2918";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2918") $ get_result_defs "vfmTestDefs2918";
val () = export_theory_no_docs ();
