open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0068Theory;
val () = new_theory "vfmTest0068";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0068") $ get_result_defs "vfmTestDefs0068";
val () = export_theory_no_docs ();
