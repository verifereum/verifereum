open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1736Theory;
val () = new_theory "vfmTest1736";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1736") $ get_result_defs "vfmTestDefs1736";
val () = export_theory_no_docs ();
