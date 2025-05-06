open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1752Theory;
val () = new_theory "vfmTest1752";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1752") $ get_result_defs "vfmTestDefs1752";
val () = export_theory_no_docs ();
