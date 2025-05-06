open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0589Theory;
val () = new_theory "vfmTest0589";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0589") $ get_result_defs "vfmTestDefs0589";
val () = export_theory_no_docs ();
