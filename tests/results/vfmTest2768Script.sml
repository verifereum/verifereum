open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2768Theory;
val () = new_theory "vfmTest2768";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2768") $ get_result_defs "vfmTestDefs2768";
val () = export_theory_no_docs ();
