open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2442Theory;
val () = new_theory "vfmTest2442";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2442") $ get_result_defs "vfmTestDefs2442";
val () = export_theory_no_docs ();
