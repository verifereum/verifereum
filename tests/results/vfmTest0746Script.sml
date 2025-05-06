open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0746Theory;
val () = new_theory "vfmTest0746";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0746") $ get_result_defs "vfmTestDefs0746";
val () = export_theory_no_docs ();
