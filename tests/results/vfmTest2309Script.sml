open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2309Theory;
val () = new_theory "vfmTest2309";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2309") $ get_result_defs "vfmTestDefs2309";
val () = export_theory_no_docs ();
