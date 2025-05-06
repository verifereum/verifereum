open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0302Theory;
val () = new_theory "vfmTest0302";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0302") $ get_result_defs "vfmTestDefs0302";
val () = export_theory_no_docs ();
