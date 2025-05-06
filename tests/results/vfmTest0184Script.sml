open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0184Theory;
val () = new_theory "vfmTest0184";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0184") $ get_result_defs "vfmTestDefs0184";
val () = export_theory_no_docs ();
