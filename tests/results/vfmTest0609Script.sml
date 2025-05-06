open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0609Theory;
val () = new_theory "vfmTest0609";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0609") $ get_result_defs "vfmTestDefs0609";
val () = export_theory_no_docs ();
