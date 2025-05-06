open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1488Theory;
val () = new_theory "vfmTest1488";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1488") $ get_result_defs "vfmTestDefs1488";
val () = export_theory_no_docs ();
