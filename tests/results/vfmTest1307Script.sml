open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1307Theory;
val () = new_theory "vfmTest1307";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1307") $ get_result_defs "vfmTestDefs1307";
val () = export_theory_no_docs ();
