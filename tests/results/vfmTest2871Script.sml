open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2871Theory;
val () = new_theory "vfmTest2871";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2871") $ get_result_defs "vfmTestDefs2871";
val () = export_theory_no_docs ();
