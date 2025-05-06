open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2462Theory;
val () = new_theory "vfmTest2462";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2462") $ get_result_defs "vfmTestDefs2462";
val () = export_theory_no_docs ();
