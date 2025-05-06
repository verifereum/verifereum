open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0804Theory;
val () = new_theory "vfmTest0804";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0804") $ get_result_defs "vfmTestDefs0804";
val () = export_theory_no_docs ();
