open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0515Theory;
val () = new_theory "vfmTest0515";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0515") $ get_result_defs "vfmTestDefs0515";
val () = export_theory_no_docs ();
