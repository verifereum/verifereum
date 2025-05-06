open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1816Theory;
val () = new_theory "vfmTest1816";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1816") $ get_result_defs "vfmTestDefs1816";
val () = export_theory_no_docs ();
