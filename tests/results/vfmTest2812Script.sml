open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2812Theory;
val () = new_theory "vfmTest2812";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2812") $ get_result_defs "vfmTestDefs2812";
val () = export_theory_no_docs ();
