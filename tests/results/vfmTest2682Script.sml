open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2682Theory;
val () = new_theory "vfmTest2682";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2682") $ get_result_defs "vfmTestDefs2682";
val () = export_theory_no_docs ();
