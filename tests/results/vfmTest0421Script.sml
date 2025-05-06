open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0421Theory;
val () = new_theory "vfmTest0421";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0421") $ get_result_defs "vfmTestDefs0421";
val () = export_theory_no_docs ();
