Theory vfmTest0689[no_sig_docs]
Ancestors vfmTestDefs0689
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0689";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
