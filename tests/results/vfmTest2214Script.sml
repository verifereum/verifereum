open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2214Theory;
val () = new_theory "vfmTest2214";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2214") $ get_result_defs "vfmTestDefs2214";
val () = export_theory_no_docs ();
