open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2003Theory;
val () = new_theory "vfmTest2003";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2003") $ get_result_defs "vfmTestDefs2003";
val () = export_theory_no_docs ();
