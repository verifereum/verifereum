open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0909Theory;
val () = new_theory "vfmTest0909";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0909") $ get_result_defs "vfmTestDefs0909";
val () = export_theory_no_docs ();
