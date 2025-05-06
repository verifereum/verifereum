open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2879Theory;
val () = new_theory "vfmTest2879";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2879") $ get_result_defs "vfmTestDefs2879";
val () = export_theory_no_docs ();
