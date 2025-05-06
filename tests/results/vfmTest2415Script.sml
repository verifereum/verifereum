open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2415Theory;
val () = new_theory "vfmTest2415";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2415") $ get_result_defs "vfmTestDefs2415";
val () = export_theory_no_docs ();
