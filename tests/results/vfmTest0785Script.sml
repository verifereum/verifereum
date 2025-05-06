open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0785Theory;
val () = new_theory "vfmTest0785";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0785") $ get_result_defs "vfmTestDefs0785";
val () = export_theory_no_docs ();
