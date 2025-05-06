open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2652Theory;
val () = new_theory "vfmTest2652";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2652") $ get_result_defs "vfmTestDefs2652";
val () = export_theory_no_docs ();
