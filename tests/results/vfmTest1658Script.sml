open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1658Theory;
val () = new_theory "vfmTest1658";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1658") $ get_result_defs "vfmTestDefs1658";
val () = export_theory_no_docs ();
