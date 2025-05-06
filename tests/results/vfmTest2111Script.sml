open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2111Theory;
val () = new_theory "vfmTest2111";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2111") $ get_result_defs "vfmTestDefs2111";
val () = export_theory_no_docs ();
