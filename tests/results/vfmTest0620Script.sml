open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0620Theory;
val () = new_theory "vfmTest0620";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0620") $ get_result_defs "vfmTestDefs0620";
val () = export_theory_no_docs ();
