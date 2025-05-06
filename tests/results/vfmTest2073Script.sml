open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2073Theory;
val () = new_theory "vfmTest2073";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2073") $ get_result_defs "vfmTestDefs2073";
val () = export_theory_no_docs ();
