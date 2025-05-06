open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2099Theory;
val () = new_theory "vfmTest2099";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2099") $ get_result_defs "vfmTestDefs2099";
val () = export_theory_no_docs ();
