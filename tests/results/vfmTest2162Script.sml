open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2162Theory;
val () = new_theory "vfmTest2162";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2162") $ get_result_defs "vfmTestDefs2162";
val () = export_theory_no_docs ();
