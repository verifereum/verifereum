open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2215Theory;
val () = new_theory "vfmTest2215";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2215") $ get_result_defs "vfmTestDefs2215";
val () = export_theory_no_docs ();
