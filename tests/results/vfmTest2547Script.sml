open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2547Theory;
val () = new_theory "vfmTest2547";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2547") $ get_result_defs "vfmTestDefs2547";
val () = export_theory_no_docs ();
