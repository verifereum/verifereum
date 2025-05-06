open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0293Theory;
val () = new_theory "vfmTest0293";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0293") $ get_result_defs "vfmTestDefs0293";
val () = export_theory_no_docs ();
