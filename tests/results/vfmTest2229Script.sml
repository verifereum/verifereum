open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2229Theory;
val () = new_theory "vfmTest2229";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2229") $ get_result_defs "vfmTestDefs2229";
val () = export_theory_no_docs ();
