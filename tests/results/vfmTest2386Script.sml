open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2386Theory;
val () = new_theory "vfmTest2386";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2386") $ get_result_defs "vfmTestDefs2386";
val () = export_theory_no_docs ();
