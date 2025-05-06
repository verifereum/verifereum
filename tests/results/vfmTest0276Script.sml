open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0276Theory;
val () = new_theory "vfmTest0276";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0276") $ get_result_defs "vfmTestDefs0276";
val () = export_theory_no_docs ();
