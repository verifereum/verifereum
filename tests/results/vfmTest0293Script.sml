open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0293Theory;
val () = new_theory "vfmTest0293";
val thyn = "vfmTestDefs0293";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
