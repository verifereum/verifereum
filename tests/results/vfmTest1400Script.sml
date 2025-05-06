open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1400Theory;
val () = new_theory "vfmTest1400";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1400") $ get_result_defs "vfmTestDefs1400";
val () = export_theory_no_docs ();
