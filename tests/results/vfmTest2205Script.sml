open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2205Theory;
val () = new_theory "vfmTest2205";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2205") $ get_result_defs "vfmTestDefs2205";
val () = export_theory_no_docs ();
