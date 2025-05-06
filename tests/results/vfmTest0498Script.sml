open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0498Theory;
val () = new_theory "vfmTest0498";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0498") $ get_result_defs "vfmTestDefs0498";
val () = export_theory_no_docs ();
