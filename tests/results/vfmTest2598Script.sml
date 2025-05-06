open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2598Theory;
val () = new_theory "vfmTest2598";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2598") $ get_result_defs "vfmTestDefs2598";
val () = export_theory_no_docs ();
