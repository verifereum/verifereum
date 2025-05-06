open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2599Theory;
val () = new_theory "vfmTest2599";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2599") $ get_result_defs "vfmTestDefs2599";
val () = export_theory_no_docs ();
