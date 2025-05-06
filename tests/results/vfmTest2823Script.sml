open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2823Theory;
val () = new_theory "vfmTest2823";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2823") $ get_result_defs "vfmTestDefs2823";
val () = export_theory_no_docs ();
