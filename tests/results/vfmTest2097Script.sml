open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2097Theory;
val () = new_theory "vfmTest2097";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2097") $ get_result_defs "vfmTestDefs2097";
val () = export_theory_no_docs ();
