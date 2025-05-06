open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2406Theory;
val () = new_theory "vfmTest2406";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2406") $ get_result_defs "vfmTestDefs2406";
val () = export_theory_no_docs ();
