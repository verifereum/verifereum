open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0256Theory;
val () = new_theory "vfmTest0256";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0256") $ get_result_defs "vfmTestDefs0256";
val () = export_theory_no_docs ();
