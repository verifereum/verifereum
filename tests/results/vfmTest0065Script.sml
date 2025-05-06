open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0065Theory;
val () = new_theory "vfmTest0065";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0065") $ get_result_defs "vfmTestDefs0065";
val () = export_theory_no_docs ();
