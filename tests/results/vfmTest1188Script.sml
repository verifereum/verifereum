open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1188Theory;
val () = new_theory "vfmTest1188";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1188") $ get_result_defs "vfmTestDefs1188";
val () = export_theory_no_docs ();
