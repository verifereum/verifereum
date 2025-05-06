open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2859Theory;
val () = new_theory "vfmTest2859";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2859") $ get_result_defs "vfmTestDefs2859";
val () = export_theory_no_docs ();
