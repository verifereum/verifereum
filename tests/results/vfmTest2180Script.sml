open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2180Theory;
val () = new_theory "vfmTest2180";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2180") $ get_result_defs "vfmTestDefs2180";
val () = export_theory_no_docs ();
