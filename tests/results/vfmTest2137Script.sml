open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2137Theory;
val () = new_theory "vfmTest2137";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2137") $ get_result_defs "vfmTestDefs2137";
val () = export_theory_no_docs ();
