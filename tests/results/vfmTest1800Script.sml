open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1800Theory;
val () = new_theory "vfmTest1800";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1800") $ get_result_defs "vfmTestDefs1800";
val () = export_theory_no_docs ();
