open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2259Theory;
val () = new_theory "vfmTest2259";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2259") $ get_result_defs "vfmTestDefs2259";
val () = export_theory_no_docs ();
