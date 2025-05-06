open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2282Theory;
val () = new_theory "vfmTest2282";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2282") $ get_result_defs "vfmTestDefs2282";
val () = export_theory_no_docs ();
