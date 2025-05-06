open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2333Theory;
val () = new_theory "vfmTest2333";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2333") $ get_result_defs "vfmTestDefs2333";
val () = export_theory_no_docs ();
