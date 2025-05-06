open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0238Theory;
val () = new_theory "vfmTest0238";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0238") $ get_result_defs "vfmTestDefs0238";
val () = export_theory_no_docs ();
