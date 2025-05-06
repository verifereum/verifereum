open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2192Theory;
val () = new_theory "vfmTest2192";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2192") $ get_result_defs "vfmTestDefs2192";
val () = export_theory_no_docs ();
