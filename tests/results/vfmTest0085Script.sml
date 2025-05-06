open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0085Theory;
val () = new_theory "vfmTest0085";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0085") $ get_result_defs "vfmTestDefs0085";
val () = export_theory_no_docs ();
