Theory vfmTest0509[no_sig_docs]
Ancestors vfmTestDefs0509
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0509";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
