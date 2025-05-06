open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0545Theory;
val () = new_theory "vfmTest0545";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0545") $ get_result_defs "vfmTestDefs0545";
val () = export_theory_no_docs ();
