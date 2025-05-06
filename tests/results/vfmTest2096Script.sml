open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2096Theory;
val () = new_theory "vfmTest2096";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2096") $ get_result_defs "vfmTestDefs2096";
val () = export_theory_no_docs ();
