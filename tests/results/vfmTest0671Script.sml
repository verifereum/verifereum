open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0671Theory;
val () = new_theory "vfmTest0671";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0671") $ get_result_defs "vfmTestDefs0671";
val () = export_theory_no_docs ();
