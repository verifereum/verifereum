open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2070Theory;
val () = new_theory "vfmTest2070";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2070") $ get_result_defs "vfmTestDefs2070";
val () = export_theory_no_docs ();
