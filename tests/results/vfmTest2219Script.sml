open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2219Theory;
val () = new_theory "vfmTest2219";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2219") $ get_result_defs "vfmTestDefs2219";
val () = export_theory_no_docs ();
