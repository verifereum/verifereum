open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2883Theory;
val () = new_theory "vfmTest2883";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2883") $ get_result_defs "vfmTestDefs2883";
val () = export_theory_no_docs ();
