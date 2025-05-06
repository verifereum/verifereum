open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2641Theory;
val () = new_theory "vfmTest2641";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2641") $ get_result_defs "vfmTestDefs2641";
val () = export_theory_no_docs ();
