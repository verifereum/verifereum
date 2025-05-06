open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2923Theory;
val () = new_theory "vfmTest2923";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2923") $ get_result_defs "vfmTestDefs2923";
val () = export_theory_no_docs ();
