open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1844Theory;
val () = new_theory "vfmTest1844";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1844") $ get_result_defs "vfmTestDefs1844";
val () = export_theory_no_docs ();
