open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1877Theory;
val () = new_theory "vfmTest1877";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1877") $ get_result_defs "vfmTestDefs1877";
val () = export_theory_no_docs ();
