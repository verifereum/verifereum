Theory vfmTest0821[no_sig_docs]
Ancestors vfmTestDefs0821
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0821";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
