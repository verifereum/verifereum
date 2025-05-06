open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1105Theory;
val () = new_theory "vfmTest1105";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1105") $ get_result_defs "vfmTestDefs1105";
val () = export_theory_no_docs ();
