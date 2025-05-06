open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1714Theory;
val () = new_theory "vfmTest1714";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1714") $ get_result_defs "vfmTestDefs1714";
val () = export_theory_no_docs ();
