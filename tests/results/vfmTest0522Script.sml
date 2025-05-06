open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0522Theory;
val () = new_theory "vfmTest0522";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0522") $ get_result_defs "vfmTestDefs0522";
val () = export_theory_no_docs ();
