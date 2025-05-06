open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0611Theory;
val () = new_theory "vfmTest0611";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0611") $ get_result_defs "vfmTestDefs0611";
val () = export_theory_no_docs ();
