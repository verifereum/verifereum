open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1725Theory;
val () = new_theory "vfmTest1725";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1725") $ get_result_defs "vfmTestDefs1725";
val () = export_theory_no_docs ();
