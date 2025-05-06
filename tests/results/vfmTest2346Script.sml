open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2346Theory;
val () = new_theory "vfmTest2346";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2346") $ get_result_defs "vfmTestDefs2346";
val () = export_theory_no_docs ();
