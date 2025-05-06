open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0561Theory;
val () = new_theory "vfmTest0561";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0561") $ get_result_defs "vfmTestDefs0561";
val () = export_theory_no_docs ();
