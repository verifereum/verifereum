Theory vfmTest0006[no_sig_docs]
Ancestors vfmTestDefs0006
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0006";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
