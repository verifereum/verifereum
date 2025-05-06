open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2347Theory;
val () = new_theory "vfmTest2347";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2347") $ get_result_defs "vfmTestDefs2347";
val () = export_theory_no_docs ();
