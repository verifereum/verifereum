open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0660Theory;
val () = new_theory "vfmTest0660";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0660") $ get_result_defs "vfmTestDefs0660";
val () = export_theory_no_docs ();
