open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0784Theory;
val () = new_theory "vfmTest0784";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0784") $ get_result_defs "vfmTestDefs0784";
val () = export_theory_no_docs ();
