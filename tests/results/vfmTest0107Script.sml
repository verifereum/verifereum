open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0107Theory;
val () = new_theory "vfmTest0107";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0107") $ get_result_defs "vfmTestDefs0107";
val () = export_theory_no_docs ();
