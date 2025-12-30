Theory vfmTest2807[no_sig_docs]
Ancestors vfmTestDefs2807
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2807";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
