open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2312Theory;
val () = new_theory "vfmTest2312";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2312") $ get_result_defs "vfmTestDefs2312";
val () = export_theory_no_docs ();
