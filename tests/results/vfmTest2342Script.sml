open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2342Theory;
val () = new_theory "vfmTest2342";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2342") $ get_result_defs "vfmTestDefs2342";
val () = export_theory_no_docs ();
