open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0111Theory;
val () = new_theory "vfmTest0111";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0111") $ get_result_defs "vfmTestDefs0111";
val () = export_theory_no_docs ();
