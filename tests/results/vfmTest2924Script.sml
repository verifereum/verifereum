open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2924Theory;
val () = new_theory "vfmTest2924";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2924") $ get_result_defs "vfmTestDefs2924";
val () = export_theory_no_docs ();
