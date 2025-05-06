open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2673Theory;
val () = new_theory "vfmTest2673";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2673") $ get_result_defs "vfmTestDefs2673";
val () = export_theory_no_docs ();
