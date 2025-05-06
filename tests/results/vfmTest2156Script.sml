open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2156Theory;
val () = new_theory "vfmTest2156";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2156") $ get_result_defs "vfmTestDefs2156";
val () = export_theory_no_docs ();
