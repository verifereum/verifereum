open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2089Theory;
val () = new_theory "vfmTest2089";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2089") $ get_result_defs "vfmTestDefs2089";
val () = export_theory_no_docs ();
