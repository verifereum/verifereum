open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2217Theory;
val () = new_theory "vfmTest2217";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2217") $ get_result_defs "vfmTestDefs2217";
val () = export_theory_no_docs ();
