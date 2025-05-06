open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2701Theory;
val () = new_theory "vfmTest2701";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2701") $ get_result_defs "vfmTestDefs2701";
val () = export_theory_no_docs ();
