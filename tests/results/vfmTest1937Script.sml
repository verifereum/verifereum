open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1937Theory;
val () = new_theory "vfmTest1937";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1937") $ get_result_defs "vfmTestDefs1937";
val () = export_theory_no_docs ();
