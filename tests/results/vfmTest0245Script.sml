open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0245Theory;
val () = new_theory "vfmTest0245";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0245") $ get_result_defs "vfmTestDefs0245";
val () = export_theory_no_docs ();
