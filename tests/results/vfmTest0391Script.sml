open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0391Theory;
val () = new_theory "vfmTest0391";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0391") $ get_result_defs "vfmTestDefs0391";
val () = export_theory_no_docs ();
