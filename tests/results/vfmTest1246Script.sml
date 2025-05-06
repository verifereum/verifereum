open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1246Theory;
val () = new_theory "vfmTest1246";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1246") $ get_result_defs "vfmTestDefs1246";
val () = export_theory_no_docs ();
