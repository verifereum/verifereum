open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2784Theory;
val () = new_theory "vfmTest2784";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2784") $ get_result_defs "vfmTestDefs2784";
val () = export_theory_no_docs ();
