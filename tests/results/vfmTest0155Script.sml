open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0155Theory;
val () = new_theory "vfmTest0155";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0155") $ get_result_defs "vfmTestDefs0155";
val () = export_theory_no_docs ();
