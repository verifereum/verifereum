open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2302Theory;
val () = new_theory "vfmTest2302";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2302") $ get_result_defs "vfmTestDefs2302";
val () = export_theory_no_docs ();
