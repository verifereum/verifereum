open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2129Theory;
val () = new_theory "vfmTest2129";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2129") $ get_result_defs "vfmTestDefs2129";
val () = export_theory_no_docs ();
