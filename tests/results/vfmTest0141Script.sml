Theory vfmTest0141[no_sig_docs]
Ancestors vfmTestDefs0141
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0141";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
