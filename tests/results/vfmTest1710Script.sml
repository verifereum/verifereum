open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1710Theory;
val () = new_theory "vfmTest1710";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1710") $ get_result_defs "vfmTestDefs1710";
val () = export_theory_no_docs ();
