open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0865Theory;
val () = new_theory "vfmTest0865";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0865") $ get_result_defs "vfmTestDefs0865";
val () = export_theory_no_docs ();
