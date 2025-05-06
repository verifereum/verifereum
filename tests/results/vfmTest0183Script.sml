open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0183Theory;
val () = new_theory "vfmTest0183";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0183") $ get_result_defs "vfmTestDefs0183";
val () = export_theory_no_docs ();
