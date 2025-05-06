open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0682Theory;
val () = new_theory "vfmTest0682";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0682") $ get_result_defs "vfmTestDefs0682";
val () = export_theory_no_docs ();
