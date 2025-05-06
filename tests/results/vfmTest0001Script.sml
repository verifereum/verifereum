open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0001Theory;
val () = new_theory "vfmTest0001";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0001") $ get_result_defs "vfmTestDefs0001";
val () = export_theory_no_docs ();
