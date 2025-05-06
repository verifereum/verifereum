open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0756Theory;
val () = new_theory "vfmTest0756";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0756") $ get_result_defs "vfmTestDefs0756";
val () = export_theory_no_docs ();
