open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2834Theory;
val () = new_theory "vfmTest2834";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2834") $ get_result_defs "vfmTestDefs2834";
val () = export_theory_no_docs ();
