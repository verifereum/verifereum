open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2486Theory;
val () = new_theory "vfmTest2486";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2486") $ get_result_defs "vfmTestDefs2486";
val () = export_theory_no_docs ();
