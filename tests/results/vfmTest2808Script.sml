open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2808Theory;
val () = new_theory "vfmTest2808";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2808") $ get_result_defs "vfmTestDefs2808";
val () = export_theory_no_docs ();
