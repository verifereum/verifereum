open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1129Theory;
val () = new_theory "vfmTest1129";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1129") $ get_result_defs "vfmTestDefs1129";
val () = export_theory_no_docs ();
