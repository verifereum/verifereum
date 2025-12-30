Theory vfmTest0875[no_sig_docs]
Ancestors vfmTestDefs0875
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0875";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
