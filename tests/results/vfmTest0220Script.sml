open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0220Theory;
val () = new_theory "vfmTest0220";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0220") $ get_result_defs "vfmTestDefs0220";
val () = export_theory_no_docs ();
