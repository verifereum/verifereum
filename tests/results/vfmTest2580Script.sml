open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2580Theory;
val () = new_theory "vfmTest2580";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2580") $ get_result_defs "vfmTestDefs2580";
val () = export_theory_no_docs ();
