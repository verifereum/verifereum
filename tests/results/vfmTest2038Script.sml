open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2038Theory;
val () = new_theory "vfmTest2038";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2038") $ get_result_defs "vfmTestDefs2038";
val () = export_theory_no_docs ();
