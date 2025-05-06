open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1673Theory;
val () = new_theory "vfmTest1673";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1673") $ get_result_defs "vfmTestDefs1673";
val () = export_theory_no_docs ();
