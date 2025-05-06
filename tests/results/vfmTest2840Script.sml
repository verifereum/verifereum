open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2840Theory;
val () = new_theory "vfmTest2840";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2840") $ get_result_defs "vfmTestDefs2840";
val () = export_theory_no_docs ();
