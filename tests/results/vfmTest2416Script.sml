open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2416Theory;
val () = new_theory "vfmTest2416";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2416") $ get_result_defs "vfmTestDefs2416";
val () = export_theory_no_docs ();
