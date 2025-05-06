open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2494Theory;
val () = new_theory "vfmTest2494";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2494") $ get_result_defs "vfmTestDefs2494";
val () = export_theory_no_docs ();
