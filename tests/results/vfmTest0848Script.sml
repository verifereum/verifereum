open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0848Theory;
val () = new_theory "vfmTest0848";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0848") $ get_result_defs "vfmTestDefs0848";
val () = export_theory_no_docs ();
