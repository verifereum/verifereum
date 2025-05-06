open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1426Theory;
val () = new_theory "vfmTest1426";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1426") $ get_result_defs "vfmTestDefs1426";
val () = export_theory_no_docs ();
