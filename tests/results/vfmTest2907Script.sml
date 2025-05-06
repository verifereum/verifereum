open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2907Theory;
val () = new_theory "vfmTest2907";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2907") $ get_result_defs "vfmTestDefs2907";
val () = export_theory_no_docs ();
