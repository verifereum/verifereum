open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1421Theory;
val () = new_theory "vfmTest1421";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1421") $ get_result_defs "vfmTestDefs1421";
val () = export_theory_no_docs ();
