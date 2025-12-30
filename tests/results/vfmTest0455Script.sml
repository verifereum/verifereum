Theory vfmTest0455[no_sig_docs]
Ancestors vfmTestDefs0455
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0455";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
