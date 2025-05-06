open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1084Theory;
val () = new_theory "vfmTest1084";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1084") $ get_result_defs "vfmTestDefs1084";
val () = export_theory_no_docs ();
