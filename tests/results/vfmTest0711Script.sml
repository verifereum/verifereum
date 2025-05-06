open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0711Theory;
val () = new_theory "vfmTest0711";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0711") $ get_result_defs "vfmTestDefs0711";
val () = export_theory_no_docs ();
