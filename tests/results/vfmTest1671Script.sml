open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1671Theory;
val () = new_theory "vfmTest1671";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1671") $ get_result_defs "vfmTestDefs1671";
val () = export_theory_no_docs ();
