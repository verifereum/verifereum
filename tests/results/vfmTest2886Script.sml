open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2886Theory;
val () = new_theory "vfmTest2886";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2886") $ get_result_defs "vfmTestDefs2886";
val () = export_theory_no_docs ();
