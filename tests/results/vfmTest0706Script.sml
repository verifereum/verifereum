open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0706Theory;
val () = new_theory "vfmTest0706";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0706") $ get_result_defs "vfmTestDefs0706";
val () = export_theory_no_docs ();
