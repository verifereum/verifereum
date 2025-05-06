open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1891Theory;
val () = new_theory "vfmTest1891";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1891") $ get_result_defs "vfmTestDefs1891";
val () = export_theory_no_docs ();
