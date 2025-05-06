open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2260Theory;
val () = new_theory "vfmTest2260";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2260") $ get_result_defs "vfmTestDefs2260";
val () = export_theory_no_docs ();
