open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2804Theory;
val () = new_theory "vfmTest2804";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2804") $ get_result_defs "vfmTestDefs2804";
val () = export_theory_no_docs ();
