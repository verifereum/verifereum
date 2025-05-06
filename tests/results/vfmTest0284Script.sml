open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0284Theory;
val () = new_theory "vfmTest0284";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0284") $ get_result_defs "vfmTestDefs0284";
val () = export_theory_no_docs ();
