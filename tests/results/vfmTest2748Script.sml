open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2748Theory;
val () = new_theory "vfmTest2748";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2748") $ get_result_defs "vfmTestDefs2748";
val () = export_theory_no_docs ();
