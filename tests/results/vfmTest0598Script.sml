open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0598Theory;
val () = new_theory "vfmTest0598";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0598") $ get_result_defs "vfmTestDefs0598";
val () = export_theory_no_docs ();
