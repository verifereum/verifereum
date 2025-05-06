open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1837Theory;
val () = new_theory "vfmTest1837";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1837") $ get_result_defs "vfmTestDefs1837";
val () = export_theory_no_docs ();
