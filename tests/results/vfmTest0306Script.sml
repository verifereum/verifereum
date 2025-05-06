open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0306Theory;
val () = new_theory "vfmTest0306";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0306") $ get_result_defs "vfmTestDefs0306";
val () = export_theory_no_docs ();
