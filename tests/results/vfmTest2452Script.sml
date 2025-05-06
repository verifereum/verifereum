open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2452Theory;
val () = new_theory "vfmTest2452";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2452") $ get_result_defs "vfmTestDefs2452";
val () = export_theory_no_docs ();
