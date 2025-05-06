open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2515Theory;
val () = new_theory "vfmTest2515";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2515") $ get_result_defs "vfmTestDefs2515";
val () = export_theory_no_docs ();
