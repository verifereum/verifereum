open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2080Theory;
val () = new_theory "vfmTest2080";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2080") $ get_result_defs "vfmTestDefs2080";
val () = export_theory_no_docs ();
