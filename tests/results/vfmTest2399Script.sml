open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2399Theory;
val () = new_theory "vfmTest2399";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2399") $ get_result_defs "vfmTestDefs2399";
val () = export_theory_no_docs ();
