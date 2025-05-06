open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2307Theory;
val () = new_theory "vfmTest2307";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2307") $ get_result_defs "vfmTestDefs2307";
val () = export_theory_no_docs ();
