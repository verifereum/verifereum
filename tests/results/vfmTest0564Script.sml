open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0564Theory;
val () = new_theory "vfmTest0564";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0564") $ get_result_defs "vfmTestDefs0564";
val () = export_theory_no_docs ();
