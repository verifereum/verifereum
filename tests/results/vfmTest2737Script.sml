open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2737Theory;
val () = new_theory "vfmTest2737";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2737") $ get_result_defs "vfmTestDefs2737";
val () = export_theory_no_docs ();
