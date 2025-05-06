open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2134Theory;
val () = new_theory "vfmTest2134";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2134") $ get_result_defs "vfmTestDefs2134";
val () = export_theory_no_docs ();
