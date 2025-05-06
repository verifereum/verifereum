open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1792Theory;
val () = new_theory "vfmTest1792";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1792") $ get_result_defs "vfmTestDefs1792";
val () = export_theory_no_docs ();
