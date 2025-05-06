open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1344Theory;
val () = new_theory "vfmTest1344";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1344") $ get_result_defs "vfmTestDefs1344";
val () = export_theory_no_docs ();
