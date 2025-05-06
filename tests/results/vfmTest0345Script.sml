open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0345Theory;
val () = new_theory "vfmTest0345";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0345") $ get_result_defs "vfmTestDefs0345";
val () = export_theory_no_docs ();
