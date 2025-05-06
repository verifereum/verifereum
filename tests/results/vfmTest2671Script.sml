open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2671Theory;
val () = new_theory "vfmTest2671";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2671") $ get_result_defs "vfmTestDefs2671";
val () = export_theory_no_docs ();
