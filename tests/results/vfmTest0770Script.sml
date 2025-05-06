open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0770Theory;
val () = new_theory "vfmTest0770";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0770") $ get_result_defs "vfmTestDefs0770";
val () = export_theory_no_docs ();
