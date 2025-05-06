open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2153Theory;
val () = new_theory "vfmTest2153";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2153") $ get_result_defs "vfmTestDefs2153";
val () = export_theory_no_docs ();
