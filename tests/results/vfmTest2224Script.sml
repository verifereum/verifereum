open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2224Theory;
val () = new_theory "vfmTest2224";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2224") $ get_result_defs "vfmTestDefs2224";
val () = export_theory_no_docs ();
