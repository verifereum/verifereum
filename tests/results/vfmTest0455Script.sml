open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0455Theory;
val () = new_theory "vfmTest0455";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0455") $ get_result_defs "vfmTestDefs0455";
val () = export_theory_no_docs ();
