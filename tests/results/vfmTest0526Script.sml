open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0526Theory;
val () = new_theory "vfmTest0526";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0526") $ get_result_defs "vfmTestDefs0526";
val () = export_theory_no_docs ();
