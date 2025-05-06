open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2826Theory;
val () = new_theory "vfmTest2826";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2826") $ get_result_defs "vfmTestDefs2826";
val () = export_theory_no_docs ();
