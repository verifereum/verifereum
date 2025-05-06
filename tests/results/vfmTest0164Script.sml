open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0164Theory;
val () = new_theory "vfmTest0164";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0164") $ get_result_defs "vfmTestDefs0164";
val () = export_theory_no_docs ();
