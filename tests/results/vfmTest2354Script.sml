open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2354Theory;
val () = new_theory "vfmTest2354";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2354") $ get_result_defs "vfmTestDefs2354";
val () = export_theory_no_docs ();
