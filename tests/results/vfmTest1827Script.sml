open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1827Theory;
val () = new_theory "vfmTest1827";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1827") $ get_result_defs "vfmTestDefs1827";
val () = export_theory_no_docs ();
