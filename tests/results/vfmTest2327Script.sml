open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2327Theory;
val () = new_theory "vfmTest2327";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2327") $ get_result_defs "vfmTestDefs2327";
val () = export_theory_no_docs ();
