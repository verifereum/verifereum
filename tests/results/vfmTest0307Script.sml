open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0307Theory;
val () = new_theory "vfmTest0307";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0307") $ get_result_defs "vfmTestDefs0307";
val () = export_theory_no_docs ();
