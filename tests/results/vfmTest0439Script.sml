open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0439Theory;
val () = new_theory "vfmTest0439";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0439") $ get_result_defs "vfmTestDefs0439";
val () = export_theory_no_docs ();
