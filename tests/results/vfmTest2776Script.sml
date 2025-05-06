open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2776Theory;
val () = new_theory "vfmTest2776";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2776") $ get_result_defs "vfmTestDefs2776";
val () = export_theory_no_docs ();
