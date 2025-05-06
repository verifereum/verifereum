open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0252Theory;
val () = new_theory "vfmTest0252";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0252") $ get_result_defs "vfmTestDefs0252";
val () = export_theory_no_docs ();
