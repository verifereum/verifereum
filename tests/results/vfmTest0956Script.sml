Theory vfmTest0956[no_sig_docs]
Ancestors vfmTestDefs0956
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0956";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
