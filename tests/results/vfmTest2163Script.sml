open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2163Theory;
val () = new_theory "vfmTest2163";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2163") $ get_result_defs "vfmTestDefs2163";
val () = export_theory_no_docs ();
