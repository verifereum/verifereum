open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1759Theory;
val () = new_theory "vfmTest1759";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1759") $ get_result_defs "vfmTestDefs1759";
val () = export_theory_no_docs ();
