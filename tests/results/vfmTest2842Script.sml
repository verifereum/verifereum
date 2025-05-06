open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2842Theory;
val () = new_theory "vfmTest2842";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2842") $ get_result_defs "vfmTestDefs2842";
val () = export_theory_no_docs ();
