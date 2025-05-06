open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2656Theory;
val () = new_theory "vfmTest2656";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2656") $ get_result_defs "vfmTestDefs2656";
val () = export_theory_no_docs ();
