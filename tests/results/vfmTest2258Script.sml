open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2258Theory;
val () = new_theory "vfmTest2258";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2258") $ get_result_defs "vfmTestDefs2258";
val () = export_theory_no_docs ();
