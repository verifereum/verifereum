open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1871Theory;
val () = new_theory "vfmTest1871";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1871") $ get_result_defs "vfmTestDefs1871";
val () = export_theory_no_docs ();
