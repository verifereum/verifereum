Theory vfmTest0031[no_sig_docs]
Ancestors vfmTestDefs0031
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0031";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
