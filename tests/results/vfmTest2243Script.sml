open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2243Theory;
val () = new_theory "vfmTest2243";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2243") $ get_result_defs "vfmTestDefs2243";
val () = export_theory_no_docs ();
