open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0828Theory;
val () = new_theory "vfmTest0828";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0828") $ get_result_defs "vfmTestDefs0828";
val () = export_theory_no_docs ();
