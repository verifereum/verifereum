open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0064Theory;
val () = new_theory "vfmTest0064";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0064") $ get_result_defs "vfmTestDefs0064";
val () = export_theory_no_docs ();
