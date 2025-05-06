open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2692Theory;
val () = new_theory "vfmTest2692";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2692") $ get_result_defs "vfmTestDefs2692";
val () = export_theory_no_docs ();
