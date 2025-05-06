open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2657Theory;
val () = new_theory "vfmTest2657";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2657") $ get_result_defs "vfmTestDefs2657";
val () = export_theory_no_docs ();
