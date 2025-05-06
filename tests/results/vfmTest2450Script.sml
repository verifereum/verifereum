open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2450Theory;
val () = new_theory "vfmTest2450";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2450") $ get_result_defs "vfmTestDefs2450";
val () = export_theory_no_docs ();
