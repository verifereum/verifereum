open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0759Theory;
val () = new_theory "vfmTest0759";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0759") $ get_result_defs "vfmTestDefs0759";
val () = export_theory_no_docs ();
