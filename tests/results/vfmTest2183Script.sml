open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2183Theory;
val () = new_theory "vfmTest2183";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2183") $ get_result_defs "vfmTestDefs2183";
val () = export_theory_no_docs ();
