open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2366Theory;
val () = new_theory "vfmTest2366";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2366") $ get_result_defs "vfmTestDefs2366";
val () = export_theory_no_docs ();
