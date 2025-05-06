open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0624Theory;
val () = new_theory "vfmTest0624";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0624") $ get_result_defs "vfmTestDefs0624";
val () = export_theory_no_docs ();
