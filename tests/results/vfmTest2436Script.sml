open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2436Theory;
val () = new_theory "vfmTest2436";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2436") $ get_result_defs "vfmTestDefs2436";
val () = export_theory_no_docs ();
