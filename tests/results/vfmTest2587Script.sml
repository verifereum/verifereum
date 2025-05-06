open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2587Theory;
val () = new_theory "vfmTest2587";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2587") $ get_result_defs "vfmTestDefs2587";
val () = export_theory_no_docs ();
